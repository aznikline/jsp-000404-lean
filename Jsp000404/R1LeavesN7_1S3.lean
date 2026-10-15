import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
    (h1382 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1543 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1657 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h1658 | h1658
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1659 | h1659
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1660 | h1660
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1661 | h1661
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1662 | h1662
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1663 | h1663
            · rcases h0bigk with h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h1, h1657, h1663, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1664_1]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h1, h1657, h1663, hc01, hc45, hlam, hphi, ht0b, ht5b, p1664_1]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                rcases p1664_3 (m.d 0 1) (by simp) with h1668 | h1668
                · rcases p1664_3 (m.d 0 2) (by simp) with h1669 | h1669
                  · linarith only [h0, h1669, hlam]
                  · linarith only [h1669, h5, hlam]
                · linarith only [h1668, h2, hlam]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                rcases p1664_3 (m.d 0 1) (by simp) with h1673 | h1673
                · rcases p1664_3 (m.d 0 2) (by simp) with h1674 | h1674
                  · linarith only [h0, h1674, hlam]
                  · linarith only [h1674, h6, hlam]
                · linarith only [h1673, h3, hlam]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h0, hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h10, h1657, h1663, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p1664_1]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                rcases p1664_3 (m.d 0 1) (by simp) with h1681 | h1681
                · rcases p1664_3 (m.d 0 2) (by simp) with h1682 | h1682
                  · rcases p1664_3 (m.d 0 3) (by simp) with h1683 | h1683
                    · linarith only [h1683, h4, hlam]
                    · linarith only [h1683, h7, hlam]
                  · linarith only [h1682, h5, hlam]
                · linarith only [h1681, h2, hlam]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                rcases p1664_3 (m.d 0 1) (by simp) with h1688 | h1688
                · rcases p1664_3 (m.d 0 2) (by simp) with h1689 | h1689
                  · rcases p1664_3 (m.d 0 3) (by simp) with h1690 | h1690
                    · linarith only [h1690, h4, hlam]
                    · linarith only [h1690, h8, hlam]
                  · linarith only [h1689, h6, hlam]
                · linarith only [h1688, h3, hlam]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h1, hlam, p1664_1]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h4, hlam, p1664_1]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                rcases p1664_3 (m.d 0 1) (by simp) with h1698 | h1698
                · rcases p1664_3 (m.d 0 2) (by simp) with h1699 | h1699
                  · rcases p1664_3 (m.d 0 3) (by simp) with h1700 | h1700
                    · rcases p1664_3 (m.d 0 4) (by simp) with h1701 | h1701
                      · linarith only [h1701, h7, hlam]
                      · rcases p1664_3 (m.d 0 5) (by simp) with h1703 | h1703
                        · linarith only [h1703, h8, hlam]
                        · rcases h2bigk with h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h1543, h1662, h4, h5, hlam, p1664_1, p1705_2]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h0, h10, h1657, h1663, hc01, hc45, hlam, hphi, ht0b, ht5b, p1705_1]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            rcases p1705_3 (m.d 0 2) (by simp) with h1709 | h1709
                            · rcases p1705_3 (m.d 1 2) (by simp) with h1710 | h1710
                              · linarith only [h0, h1710, hlam]
                              · rcases p1705_3 (m.d 2 3) (by simp) with h1712 | h1712
                                · linarith only [h1712, h4, hlam]
                                · linarith only [h1660, h1712, hlam]
                            · linarith only [h1709, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            rcases p1705_3 (m.d 0 2) (by simp) with h1716 | h1716
                            · rcases p1705_3 (m.d 1 2) (by simp) with h1717 | h1717
                              · linarith only [h0, h1717, hlam]
                              · rcases p1705_3 (m.d 2 3) (by simp) with h1719 | h1719
                                · linarith only [h1719, h4, hlam]
                                · linarith only [h1661, h1719, hlam]
                            · linarith only [h1716, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h0, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h10, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h1382, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h1543, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h4, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            rcases p1705_3 (m.d 0 2) (by simp) with h1729 | h1729
                            · rcases p1705_3 (m.d 1 2) (by simp) with h1730 | h1730
                              · linarith only [h1730, hlam, p1705_0]
                              · rcases p1705_3 (m.d 2 3) (by simp) with h1732 | h1732
                                · rcases p1705_3 (m.d 2 4) (by simp) with h1733 | h1733
                                  · linarith only [h1660, h1733, hlam]
                                  · linarith only [h1382, h1733, hlam]
                                · linarith only [h1732, hlam, p1705_0]
                            · linarith only [h0, h1729, hlam]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h1543, h1662, hc12, hc23, hlam, hphi, p1705_1]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h0, h1543, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1705_1]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h5, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h0, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1664_1, p1705_1]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h1660, hlam, p1705_1]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h0, h1543, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1664_1, p1705_1]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h6, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1664_1, p1705_1]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h1661, hlam, p1705_1]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [h1662, hlam, p1705_0]
                          · have p1705_0 := h1705c.1
                            have p1705_1 := h1705c.2.1
                            have p1705_2 := h1705c.2.2.1
                            have p1705_3 := h1705c.2.2.2
                            linarith only [hlam, p1705_0]
                    · linarith only [h1700, h7, hlam]
                  · linarith only [h1699, h5, hlam]
                · linarith only [h1698, h2, hlam]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                rcases p1664_3 (m.d 0 1) (by simp) with h1754 | h1754
                · rcases p1664_3 (m.d 0 2) (by simp) with h1755 | h1755
                  · rcases p1664_3 (m.d 0 3) (by simp) with h1756 | h1756
                    · rcases p1664_3 (m.d 0 4) (by simp) with h1757 | h1757
                      · linarith only [h1757, h7, hlam]
                      · linarith only [h1757, h9, hlam]
                    · linarith only [h1756, h8, hlam]
                  · linarith only [h1755, h6, hlam]
                · linarith only [h1754, h3, hlam]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h2, hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h5, hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h7, hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                rcases p1664_3 (m.d 0 1) (by simp) with h1767 | h1767
                · rcases p1664_3 (m.d 0 2) (by simp) with h1768 | h1768
                  · rcases p1664_3 (m.d 0 3) (by simp) with h1769 | h1769
                    · rcases p1664_3 (m.d 0 4) (by simp) with h1770 | h1770
                      · rcases p1664_3 (m.d 0 5) (by simp) with h1771 | h1771
                        · linarith only [h1771, h9, hlam]
                        · rcases h2bigk with h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c | h1773c
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h1543, h5, h6, hlam, p1664_1, p1773_2]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h10, h1657, h1663, hc02, hc45, hlam, hphi, ht0b, ht5b, p1773_1]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            rcases p1773_3 (m.d 0 2) (by simp) with h1777 | h1777
                            · rcases p1773_3 (m.d 1 2) (by simp) with h1778 | h1778
                              · linarith only [h0, h1778, hlam]
                              · rcases p1773_3 (m.d 2 3) (by simp) with h1780 | h1780
                                · linarith only [h1780, h4, hlam]
                                · linarith only [h1660, h1780, hlam]
                            · linarith only [h1777, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            rcases p1773_3 (m.d 0 2) (by simp) with h1784 | h1784
                            · rcases p1773_3 (m.d 1 2) (by simp) with h1785 | h1785
                              · linarith only [h0, h1785, hlam]
                              · rcases p1773_3 (m.d 2 3) (by simp) with h1787 | h1787
                                · linarith only [h1787, h4, hlam]
                                · linarith only [h1661, h1787, hlam]
                            · linarith only [h1784, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h0, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h10, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h1382, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h1543, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h4, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            rcases p1773_3 (m.d 0 2) (by simp) with h1797 | h1797
                            · rcases p1773_3 (m.d 1 2) (by simp) with h1798 | h1798
                              · linarith only [h1798, hlam, p1773_0]
                              · rcases p1773_3 (m.d 2 3) (by simp) with h1800 | h1800
                                · rcases p1773_3 (m.d 2 4) (by simp) with h1801 | h1801
                                  · linarith only [h1660, h1801, hlam]
                                  · linarith only [h1382, h1801, hlam]
                                · linarith only [h1800, hlam, p1773_0]
                            · linarith only [h0, h1797, hlam]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h1382, hc12, hc23, hlam, hphi, p1773_1]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h0, h1543, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1773_1]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h5, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            rcases p1773_3 (m.d 0 2) (by simp) with h1810 | h1810
                            · rcases p1773_3 (m.d 1 2) (by simp) with h1811 | h1811
                              · linarith only [h1811, hlam, p1773_0]
                              · rcases p1773_3 (m.d 2 3) (by simp) with h1813 | h1813
                                · rcases p1773_3 (m.d 2 4) (by simp) with h1814 | h1814
                                  · rcases p1773_3 (m.d 2 5) (by simp) with h1815 | h1815
                                    · linarith only [h1662, h1815, hlam]
                                    · linarith only [h1543, h1815, hlam]
                                  · linarith only [h1814, hlam, p1773_0]
                                · linarith only [h10, h1813, hlam]
                            · linarith only [h0, h1810, hlam]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h1660, hlam, p1773_1]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h1543, hc12, hc24, hlam, hphi, p1773_1]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h6, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h6, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1664_1, p1773_1]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h1661, hlam, p1773_1]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [h1662, hlam, p1773_0]
                          · have p1773_0 := h1773c.1
                            have p1773_1 := h1773c.2.1
                            have p1773_2 := h1773c.2.2.1
                            have p1773_3 := h1773c.2.2.2
                            linarith only [hlam, p1773_0]
                      · linarith only [h1770, h9, hlam]
                    · linarith only [h1769, h8, hlam]
                  · linarith only [h1768, h6, hlam]
                · linarith only [h1767, h3, hlam]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h3, hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h6, hlam, p1664_1]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h8, hlam, p1664_0]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [h9, hlam, p1664_1]
              · have p1664_0 := h1664c.1
                have p1664_1 := h1664c.2.1
                have p1664_2 := h1664c.2.2.1
                have p1664_3 := h1664c.2.2.2
                linarith only [hlam, p1664_0]
            · rcases h0bigk with h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h1663, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h1663, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h1663, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                rcases p1838_3 (m.d 0 1) (by simp) with h1843 | h1843
                · rcases p1838_3 (m.d 0 2) (by simp) with h1844 | h1844
                  · linarith only [h0, h1844, hlam]
                  · linarith only [h1844, h6, hlam]
                · linarith only [h1843, h3, hlam]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h0, hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h1659, h1663, h2, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h0, h1659, h1663, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                rcases p1838_3 (m.d 0 1) (by simp) with h1852 | h1852
                · rcases p1838_3 (m.d 0 2) (by simp) with h1853 | h1853
                  · rcases p1838_3 (m.d 0 3) (by simp) with h1854 | h1854
                    · linarith only [h1854, h4, hlam]
                    · linarith only [h1854, h8, hlam]
                  · linarith only [h1853, h6, hlam]
                · linarith only [h1852, h3, hlam]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h1, hlam, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h4, hlam, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h1382, h1659, h1663, h5, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                rcases p1838_3 (m.d 0 1) (by simp) with h1863 | h1863
                · rcases p1838_3 (m.d 0 2) (by simp) with h1864 | h1864
                  · rcases p1838_3 (m.d 0 3) (by simp) with h1865 | h1865
                    · rcases p1838_3 (m.d 0 4) (by simp) with h1866 | h1866
                      · linarith only [h1866, h7, hlam]
                      · linarith only [h1866, h9, hlam]
                    · linarith only [h1865, h8, hlam]
                  · linarith only [h1864, h6, hlam]
                · linarith only [h1863, h3, hlam]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h2, hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h5, hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h7, hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                rcases p1838_3 (m.d 0 1) (by simp) with h1876 | h1876
                · rcases p1838_3 (m.d 0 2) (by simp) with h1877 | h1877
                  · rcases p1838_3 (m.d 0 3) (by simp) with h1878 | h1878
                    · rcases p1838_3 (m.d 0 4) (by simp) with h1879 | h1879
                      · rcases p1838_3 (m.d 0 5) (by simp) with h1880 | h1880
                        · linarith only [h1880, h9, hlam]
                        · rcases h2bigk with h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1543, h4, h6, h7, hlam, p1838_1, p1882_2]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h0, h1382, h1659, h1660, h1663, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h0, h1382, h1659, h1663, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            rcases p1882_3 (m.d 0 2) (by simp) with h1887 | h1887
                            · rcases p1882_3 (m.d 1 2) (by simp) with h1888 | h1888
                              · linarith only [h0, h1888, hlam]
                              · rcases p1882_3 (m.d 2 3) (by simp) with h1890 | h1890
                                · linarith only [h1890, h4, hlam]
                                · linarith only [h1661, h1890, hlam]
                            · linarith only [h1887, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h0, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h10, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1382, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1543, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h4, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            rcases p1882_3 (m.d 0 2) (by simp) with h1900 | h1900
                            · rcases p1882_3 (m.d 1 2) (by simp) with h1901 | h1901
                              · linarith only [h1901, hlam, p1882_0]
                              · rcases p1882_3 (m.d 2 3) (by simp) with h1903 | h1903
                                · rcases p1882_3 (m.d 2 4) (by simp) with h1904 | h1904
                                  · linarith only [h1660, h1904, hlam]
                                  · linarith only [h1382, h1904, hlam]
                                · linarith only [h1903, hlam, p1882_0]
                            · linarith only [h0, h1900, hlam]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h0, h1382, h1543, h1659, h1663, h4, h6, h7, hc01, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1838_1, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h0, h1543, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h5, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            rcases p1882_3 (m.d 0 2) (by simp) with h1913 | h1913
                            · rcases p1882_3 (m.d 1 2) (by simp) with h1914 | h1914
                              · linarith only [h1914, hlam, p1882_0]
                              · rcases p1882_3 (m.d 2 3) (by simp) with h1916 | h1916
                                · rcases p1882_3 (m.d 2 4) (by simp) with h1917 | h1917
                                  · rcases p1882_3 (m.d 2 5) (by simp) with h1918 | h1918
                                    · linarith only [h1662, h1918, hlam]
                                    · linarith only [h1543, h1918, hlam]
                                  · linarith only [h1917, hlam, p1882_0]
                                · linarith only [h10, h1916, hlam]
                            · linarith only [h0, h1913, hlam]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1660, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1543, hc12, hc24, hlam, hphi, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h6, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h0, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1838_1, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1661, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1662, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                      · linarith only [h1879, h9, hlam]
                    · linarith only [h1878, h8, hlam]
                  · linarith only [h1877, h6, hlam]
                · linarith only [h1876, h3, hlam]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h3, hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h6, hlam, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h8, hlam, p1838_0]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [h9, hlam, p1838_1]
              · have p1838_0 := h1838c.1
                have p1838_1 := h1838c.2.1
                have p1838_2 := h1838c.2.2.1
                have p1838_3 := h1838c.2.2.2
                linarith only [hlam, p1838_0]
          · linarith only [h1382, h1659, h1662, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h10, h1658, h1661, hlam]
      · linarith only [h10, h1657, h1660, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1944 | h1944
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1945 | h1945
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1946 | h1946
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1947 | h1947
            · linarith only [h1, h1657, h1659, h1947, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h0bigk with h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h1382, h1659, h1944, h1946, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h1382, h1659, h1944, h1946, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h1382, h1659, h1946, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                rcases p1949_3 (m.d 0 1) (by simp) with h1954 | h1954
                · rcases p1949_3 (m.d 0 2) (by simp) with h1955 | h1955
                  · linarith only [h0, h1955, hlam]
                  · linarith only [h1955, h6, hlam]
                · linarith only [h1954, h3, hlam]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h0, hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h1382, h1659, h1944, h1946, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h0, h1382, h1659, h1946, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                rcases p1949_3 (m.d 0 1) (by simp) with h1963 | h1963
                · rcases p1949_3 (m.d 0 2) (by simp) with h1964 | h1964
                  · rcases p1949_3 (m.d 0 3) (by simp) with h1965 | h1965
                    · linarith only [h1965, h4, hlam]
                    · linarith only [h1965, h8, hlam]
                  · linarith only [h1964, h6, hlam]
                · linarith only [h1963, h3, hlam]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h1, hlam, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h4, hlam, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h1382, h1659, h1946, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                rcases p1949_3 (m.d 0 1) (by simp) with h1974 | h1974
                · rcases p1949_3 (m.d 0 2) (by simp) with h1975 | h1975
                  · rcases p1949_3 (m.d 0 3) (by simp) with h1976 | h1976
                    · rcases p1949_3 (m.d 0 4) (by simp) with h1977 | h1977
                      · linarith only [h1977, h7, hlam]
                      · linarith only [h1977, h9, hlam]
                    · linarith only [h1976, h8, hlam]
                  · linarith only [h1975, h6, hlam]
                · linarith only [h1974, h3, hlam]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h2, hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h5, hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h7, hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                rcases p1949_3 (m.d 0 1) (by simp) with h1987 | h1987
                · rcases p1949_3 (m.d 0 2) (by simp) with h1988 | h1988
                  · rcases p1949_3 (m.d 0 3) (by simp) with h1989 | h1989
                    · rcases p1949_3 (m.d 0 4) (by simp) with h1990 | h1990
                      · rcases p1949_3 (m.d 0 5) (by simp) with h1991 | h1991
                        · linarith only [h1991, h9, hlam]
                        · rcases h2bigk with h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1382, h1659, h1944, h1946, h4, hlam, p1993_2]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1382, h1659, h1944, h1946, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1993_1]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h0, h1382, h1659, h1946, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1993_1]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            rcases p1993_3 (m.d 0 2) (by simp) with h1998 | h1998
                            · rcases p1993_3 (m.d 1 2) (by simp) with h1999 | h1999
                              · linarith only [h0, h1999, hlam]
                              · rcases p1993_3 (m.d 2 3) (by simp) with h2001 | h2001
                                · linarith only [h2001, h4, hlam]
                                · linarith only [h1945, h2001, hlam]
                            · linarith only [h1998, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h0, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h10, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1382, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1543, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h4, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            rcases p1993_3 (m.d 0 2) (by simp) with h2011 | h2011
                            · rcases p1993_3 (m.d 1 2) (by simp) with h2012 | h2012
                              · linarith only [h2012, hlam, p1993_0]
                              · rcases p1993_3 (m.d 2 3) (by simp) with h2014 | h2014
                                · rcases p1993_3 (m.d 2 4) (by simp) with h2015 | h2015
                                  · linarith only [h1944, h2015, hlam]
                                  · linarith only [h1382, h2015, hlam]
                                · linarith only [h2014, hlam, p1993_0]
                            · linarith only [h0, h2011, hlam]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1382, h1659, h1946, hc12, hc23, hlam, hphi, p1993_1]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h0, h1382, h1659, h1946, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1993_1]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h5, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            rcases p1993_3 (m.d 0 2) (by simp) with h2024 | h2024
                            · rcases p1993_3 (m.d 1 2) (by simp) with h2025 | h2025
                              · linarith only [h2025, hlam, p1993_0]
                              · rcases p1993_3 (m.d 2 3) (by simp) with h2027 | h2027
                                · rcases p1993_3 (m.d 2 4) (by simp) with h2028 | h2028
                                  · rcases p1993_3 (m.d 2 5) (by simp) with h2029 | h2029
                                    · linarith only [h1946, h2029, hlam]
                                    · linarith only [h1543, h2029, hlam]
                                  · linarith only [h2028, hlam, p1993_0]
                                · linarith only [h10, h2027, hlam]
                            · linarith only [h0, h2024, hlam]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1944, hlam, p1993_1]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1382, h1659, h1946, hc12, hc24, hlam, hphi, p1993_1]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h6, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1949_1, p1993_1]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1945, hlam, p1993_1]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [h1946, hlam, p1993_0]
                          · have p1993_0 := h1993c.1
                            have p1993_1 := h1993c.2.1
                            have p1993_2 := h1993c.2.2.1
                            have p1993_3 := h1993c.2.2.2
                            linarith only [hlam, p1993_0]
                      · linarith only [h1990, h9, hlam]
                    · linarith only [h1989, h8, hlam]
                  · linarith only [h1988, h6, hlam]
                · linarith only [h1987, h3, hlam]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h3, hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h6, hlam, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h8, hlam, p1949_0]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [h9, hlam, p1949_1]
              · have p1949_0 := h1949c.1
                have p1949_1 := h1949c.2.1
                have p1949_2 := h1949c.2.2.1
                have p1949_3 := h1949c.2.2.2
                linarith only [hlam, p1949_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2052 | h2052
            · linarith only [h0, h10, h1543, h1657, h1946, h2052, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h0bigk with h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h1382, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h1382, h1946, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h1382, h1946, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h1382, h1946, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h0, hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h1382, h1946, h8, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h0, h1382, h1946, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h0, h1382, h1946, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h1, hlam, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h4, hlam, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h1382, h1946, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h0, h1382, h1946, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h2, hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h5, hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h7, hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h0, h1382, h1946, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h3, hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h6, hlam, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h8, hlam, p2054_0]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [h9, hlam, p2054_1]
              · have p2054_0 := h2054c.1
                have p2054_1 := h2054c.2.1
                have p2054_2 := h2054c.2.2.1
                have p2054_3 := h2054c.2.2.2
                linarith only [hlam, p2054_0]
        · linarith only [h10, h1658, h1945, hlam]
      · linarith only [h10, h1657, h1944, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2082 | h2082
    · linarith only [h1657, h1658, h2082, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2084 | h2084
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2085 | h2085
        · linarith only [h0, h1657, h1658, h2085, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2087 | h2087
          · linarith only [h0, h2082, h2084, h2085, h2087, h4, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2089 | h2089
            · linarith only [h0, h10, h1657, h2085, h2087, h2089, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases h0bigk with h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c | h2091c
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h1382, h2084, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h1658, h2089, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h1657, h1658, h2089, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h1657, h1658, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h0, hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h1657, h1658, h2089, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h0, h1657, h1658, h2089, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h0, h1657, h1658, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h1, hlam, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h4, hlam, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h1657, h1658, h2089, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h0, h1657, h1658, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h2, hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h5, hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h7, hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h1657, h1658, h8, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h3, hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h6, hlam, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h8, hlam, p2091_0]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [h9, hlam, p2091_1]
              · have p2091_0 := h2091c.1
                have p2091_1 := h2091c.2.1
                have p2091_2 := h2091c.2.2.1
                have p2091_3 := h2091c.2.2.2
                linarith only [hlam, p2091_0]
      · linarith only [h1, h10, h1657, h2084, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

end R2N4
