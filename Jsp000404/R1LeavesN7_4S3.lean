import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1383 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1609 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1680 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h1681 | h1681
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1682 | h1682
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1683 | h1683
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1684 | h1684
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1685 | h1685
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1686 | h1686
            · rcases h1bigk with h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c | h1687c
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                rcases p1687_3 (m.d 0 1) (by simp) with h1689 | h1689
                · rcases p1687_3 (m.d 1 2) (by simp) with h1690 | h1690
                  · linarith only [h1690, hlam, p1687_0]
                  · rcases p1687_3 (m.d 1 3) (by simp) with h1692 | h1692
                    · linarith only [h1, h1692, hlam]
                    · linarith only [h1692, h9, hlam]
                · linarith only [h1689, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h1680, h1686, hc01, hc45, hlam, hphi, ht0b, ht5b, p1687_1]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                rcases p1687_3 (m.d 0 1) (by simp) with h1697 | h1697
                · rcases p1687_3 (m.d 1 2) (by simp) with h1698 | h1698
                  · linarith only [h0, h1698, hlam]
                  · rcases p1687_3 (m.d 1 3) (by simp) with h1700 | h1700
                    · linarith only [h1, h1700, hlam]
                    · linarith only [h1680, h1700, hlam]
                · linarith only [h1697, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                rcases p1687_3 (m.d 0 1) (by simp) with h1704 | h1704
                · rcases p1687_3 (m.d 1 2) (by simp) with h1705 | h1705
                  · linarith only [h0, h1705, hlam]
                  · rcases p1687_3 (m.d 1 3) (by simp) with h1707 | h1707
                    · linarith only [h1, h1707, hlam]
                    · linarith only [h1681, h1707, hlam]
                · linarith only [h1704, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h0, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h9, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h1383, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h1609, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h1, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                rcases p1687_3 (m.d 0 1) (by simp) with h1717 | h1717
                · rcases p1687_3 (m.d 1 2) (by simp) with h1718 | h1718
                  · linarith only [h1718, h9, hlam]
                  · rcases p1687_3 (m.d 1 3) (by simp) with h1720 | h1720
                    · rcases p1687_3 (m.d 1 4) (by simp) with h1721 | h1721
                      · linarith only [h1680, h1721, hlam]
                      · linarith only [h1383, h1721, hlam]
                    · linarith only [h1720, h9, hlam]
                · linarith only [h0, h1717, hlam]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h0, h1680, h1686, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p1687_1]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                rcases p1687_3 (m.d 0 1) (by simp) with h1728 | h1728
                · rcases p1687_3 (m.d 1 2) (by simp) with h1729 | h1729
                  · linarith only [h1729, h9, hlam]
                  · rcases p1687_3 (m.d 1 3) (by simp) with h1731 | h1731
                    · rcases p1687_3 (m.d 1 4) (by simp) with h1732 | h1732
                      · linarith only [h1680, h1732, hlam]
                      · linarith only [h1682, h1732, hlam]
                    · linarith only [h1681, h1731, hlam]
                · linarith only [h1728, h3, hlam]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h2, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                rcases p1687_3 (m.d 0 1) (by simp) with h1738 | h1738
                · rcases p1687_3 (m.d 1 2) (by simp) with h1739 | h1739
                  · linarith only [h1383, h1739, hlam]
                  · rcases p1687_3 (m.d 1 3) (by simp) with h1741 | h1741
                    · rcases p1687_3 (m.d 1 4) (by simp) with h1742 | h1742
                      · rcases p1687_3 (m.d 1 5) (by simp) with h1743 | h1743
                        · linarith only [h1682, h1743, hlam]
                        · linarith only [h1609, h1743, hlam]
                      · linarith only [h1383, h1742, hlam]
                    · linarith only [h1741, h9, hlam]
                · linarith only [h0, h1738, hlam]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h1680, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                rcases p1687_3 (m.d 0 1) (by simp) with h1751 | h1751
                · rcases p1687_3 (m.d 1 2) (by simp) with h1752 | h1752
                  · linarith only [h1383, h1752, hlam]
                  · rcases p1687_3 (m.d 1 3) (by simp) with h1754 | h1754
                    · rcases p1687_3 (m.d 1 4) (by simp) with h1755 | h1755
                      · rcases p1687_3 (m.d 1 5) (by simp) with h1756 | h1756
                        · linarith only [h1682, h1756, hlam]
                        · rcases h3bigk with h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h0, h1680, h1686, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h0, h1383, h1683, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p1687_1, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h0, h1686, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            rcases p1758_3 (m.d 0 3) (by simp) with h1763 | h1763
                            · rcases p1758_3 (m.d 1 3) (by simp) with h1764 | h1764
                              · linarith only [h1, h1764, hlam]
                              · linarith only [h1681, h1764, hlam]
                            · linarith only [h1763, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h1, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h9, hlam, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h1686, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h1, h1686, hc01, hc45, hlam, hphi, ht0b, ht5b, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h4, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h0, h1686, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h0, h1686, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h6, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h1680, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h1683, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h0, h1686, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p1758_1]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h7, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h1681, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h1684, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [h1686, hlam, p1758_0]
                          · have p1758_0 := h1758c.1
                            have p1758_1 := h1758c.2.1
                            have p1758_2 := h1758c.2.2.1
                            have p1758_3 := h1758c.2.2.2
                            linarith only [hlam, p1758_0]
                      · linarith only [h1682, h1755, hlam]
                    · linarith only [h1681, h1754, hlam]
                · linarith only [h1751, h3, hlam]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h3, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                rcases p1687_3 (m.d 0 1) (by simp) with h1792 | h1792
                · rcases p1687_3 (m.d 1 2) (by simp) with h1793 | h1793
                  · linarith only [h1609, h1793, hlam]
                  · rcases p1687_3 (m.d 1 3) (by simp) with h1795 | h1795
                    · rcases p1687_3 (m.d 1 4) (by simp) with h1796 | h1796
                      · rcases p1687_3 (m.d 1 5) (by simp) with h1797 | h1797
                        · rcases h3bigk with h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h0, h1680, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h0, h1686, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            rcases p1798_3 (m.d 0 3) (by simp) with h1803 | h1803
                            · rcases p1798_3 (m.d 1 3) (by simp) with h1804 | h1804
                              · linarith only [h1, h1804, hlam]
                              · linarith only [h1681, h1804, hlam]
                            · linarith only [h1803, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h1, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h9, hlam, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h1686, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h0, h1686, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h4, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h0, h1686, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h0, h1686, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h6, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h1680, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h1683, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h0, h1686, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p1798_1]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h7, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h1681, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h1684, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [h1686, hlam, p1798_0]
                          · have p1798_0 := h1798c.1
                            have p1798_1 := h1798c.2.1
                            have p1798_2 := h1798c.2.2.1
                            have p1798_3 := h1798c.2.2.2
                            linarith only [hlam, p1798_0]
                        · linarith only [h1609, h1797, hlam]
                      · linarith only [h1383, h1796, hlam]
                    · linarith only [h1795, h9, hlam]
                · linarith only [h0, h1792, hlam]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h1681, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [h1682, hlam, p1687_0]
              · have p1687_0 := h1687c.1
                have p1687_1 := h1687c.2.1
                have p1687_2 := h1687c.2.2.1
                have p1687_3 := h1687c.2.2.2
                linarith only [hlam, p1687_0]
            · rcases h1bigk with h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                rcases p1835_3 (m.d 0 1) (by simp) with h1837 | h1837
                · rcases p1835_3 (m.d 1 2) (by simp) with h1838 | h1838
                  · linarith only [h1838, hlam, p1835_0]
                  · rcases p1835_3 (m.d 1 3) (by simp) with h1840 | h1840
                    · linarith only [h1, h1840, hlam]
                    · linarith only [h1840, h9, hlam]
                · linarith only [h1837, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1680, h1682, h1686, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1835_1]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1682, h1686, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1835_1]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                rcases p1835_3 (m.d 0 1) (by simp) with h1846 | h1846
                · rcases p1835_3 (m.d 1 2) (by simp) with h1847 | h1847
                  · linarith only [h0, h1847, hlam]
                  · rcases p1835_3 (m.d 1 3) (by simp) with h1849 | h1849
                    · linarith only [h1, h1849, hlam]
                    · linarith only [h1681, h1849, hlam]
                · linarith only [h1846, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h0, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h9, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1383, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1609, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                rcases p1835_3 (m.d 0 1) (by simp) with h1859 | h1859
                · rcases p1835_3 (m.d 1 2) (by simp) with h1860 | h1860
                  · linarith only [h1860, h9, hlam]
                  · rcases p1835_3 (m.d 1 3) (by simp) with h1862 | h1862
                    · rcases p1835_3 (m.d 1 4) (by simp) with h1863 | h1863
                      · linarith only [h1680, h1863, hlam]
                      · linarith only [h1383, h1863, hlam]
                    · linarith only [h1862, h9, hlam]
                · linarith only [h0, h1859, hlam]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1682, h1686, h4, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1835_1]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h0, h1682, h1686, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1835_1]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h2, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                rcases p1835_3 (m.d 0 1) (by simp) with h1872 | h1872
                · rcases p1835_3 (m.d 1 2) (by simp) with h1873 | h1873
                  · linarith only [h1383, h1873, hlam]
                  · rcases p1835_3 (m.d 1 3) (by simp) with h1875 | h1875
                    · rcases p1835_3 (m.d 1 4) (by simp) with h1876 | h1876
                      · rcases p1835_3 (m.d 1 5) (by simp) with h1877 | h1877
                        · linarith only [h1682, h1877, hlam]
                        · linarith only [h1609, h1877, hlam]
                      · linarith only [h1383, h1876, hlam]
                    · linarith only [h1875, h9, hlam]
                · linarith only [h0, h1872, hlam]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1680, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h0, h1383, h1682, h1683, h1686, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1835_1]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h3, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                rcases p1835_3 (m.d 0 1) (by simp) with h1887 | h1887
                · rcases p1835_3 (m.d 1 2) (by simp) with h1888 | h1888
                  · linarith only [h1609, h1888, hlam]
                  · rcases p1835_3 (m.d 1 3) (by simp) with h1890 | h1890
                    · rcases p1835_3 (m.d 1 4) (by simp) with h1891 | h1891
                      · rcases p1835_3 (m.d 1 5) (by simp) with h1892 | h1892
                        · rcases h3bigk with h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h0, h1680, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h0, h1609, h1683, h1685, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1835_1, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            rcases p1893_3 (m.d 0 3) (by simp) with h1897 | h1897
                            · rcases p1893_3 (m.d 1 3) (by simp) with h1898 | h1898
                              · linarith only [h1, h1898, hlam]
                              · linarith only [h1680, h1898, hlam]
                            · linarith only [h1897, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            rcases p1893_3 (m.d 0 3) (by simp) with h1902 | h1902
                            · rcases p1893_3 (m.d 1 3) (by simp) with h1903 | h1903
                              · linarith only [h1, h1903, hlam]
                              · linarith only [h1681, h1903, hlam]
                            · linarith only [h1902, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h1, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h9, hlam, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h0, h1686, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h4, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h0, h1686, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h6, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h1680, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h1683, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h1686, hlam, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h7, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h1681, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h1684, hlam, p1893_0]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1893_1]
                          · have p1893_0 := h1893c.1
                            have p1893_1 := h1893c.2.1
                            have p1893_2 := h1893c.2.2.1
                            have p1893_3 := h1893c.2.2.2
                            linarith only [hlam, p1893_0]
                        · linarith only [h1609, h1892, hlam]
                      · linarith only [h1383, h1891, hlam]
                    · linarith only [h1890, h9, hlam]
                · linarith only [h0, h1887, hlam]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1681, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [h1682, hlam, p1835_0]
              · have p1835_0 := h1835c.1
                have p1835_1 := h1835c.2.1
                have p1835_2 := h1835c.2.2.1
                have p1835_3 := h1835c.2.2.2
                linarith only [hlam, p1835_0]
          · linarith only [h1383, h1682, h1685, hlam]
        · linarith only [h1681, h1684, h9, hlam]
      · linarith only [h1680, h1683, h9, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1937 | h1937
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1938 | h1938
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1939 | h1939
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1940 | h1940
            · linarith only [h1, h1680, h1682, h1940, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h1bigk with h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h0, h1383, h1682, h1937, h1939, h4, hlam, p1942_2]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                rcases p1942_3 (m.d 0 1) (by simp) with h1945 | h1945
                · rcases p1942_3 (m.d 1 2) (by simp) with h1946 | h1946
                  · linarith only [h0, h1946, hlam]
                  · rcases p1942_3 (m.d 1 3) (by simp) with h1948 | h1948
                    · linarith only [h1948, hlam, p1942_0]
                    · rcases p1942_3 (m.d 1 4) (by simp) with h1950 | h1950
                      · linarith only [h1950, h2, hlam]
                      · rcases p1942_3 (m.d 1 5) (by simp) with h1952 | h1952
                        · linarith only [h1952, h3, hlam]
                        · rcases h3bigk with h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h0, h1681, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h0, h1383, h1682, h1937, h1939, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            rcases p1954_3 (m.d 0 3) (by simp) with h1958 | h1958
                            · rcases p1954_3 (m.d 1 3) (by simp) with h1959 | h1959
                              · linarith only [h1, h1959, hlam]
                              · linarith only [h1680, h1959, hlam]
                            · linarith only [h1958, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            rcases p1954_3 (m.d 0 3) (by simp) with h1963 | h1963
                            · rcases p1954_3 (m.d 1 3) (by simp) with h1964 | h1964
                              · linarith only [h1, h1964, hlam]
                              · linarith only [h1681, h1964, hlam]
                            · linarith only [h1963, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h1, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h9, hlam, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1942_1, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h1940, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1942_1, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h4, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h0, h4, hlam, p1942_2, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h0, h1940, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h6, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h1680, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h1937, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h1940, hlam, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h7, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h1681, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h1938, hlam, p1954_0]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [h1681, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1954_1]
                          · have p1954_0 := h1954c.1
                            have p1954_1 := h1954c.2.1
                            have p1954_2 := h1954c.2.2.1
                            have p1954_3 := h1954c.2.2.2
                            linarith only [hlam, p1954_0]
                · linarith only [h1945, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h0, h1682, h1939, h5, hlam, p1942_2]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                rcases p1942_3 (m.d 0 1) (by simp) with h1990 | h1990
                · rcases p1942_3 (m.d 1 2) (by simp) with h1991 | h1991
                  · linarith only [h0, h1991, hlam]
                  · rcases p1942_3 (m.d 1 3) (by simp) with h1993 | h1993
                    · linarith only [h1, h1993, hlam]
                    · linarith only [h1681, h1993, hlam]
                · linarith only [h1990, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h0, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h9, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h1383, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h1609, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h1, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                rcases p1942_3 (m.d 0 1) (by simp) with h2003 | h2003
                · rcases p1942_3 (m.d 1 2) (by simp) with h2004 | h2004
                  · linarith only [h2004, h9, hlam]
                  · rcases p1942_3 (m.d 1 3) (by simp) with h2006 | h2006
                    · rcases p1942_3 (m.d 1 4) (by simp) with h2007 | h2007
                      · linarith only [h1680, h2007, hlam]
                      · linarith only [h1383, h2007, hlam]
                    · linarith only [h2006, h9, hlam]
                · linarith only [h0, h2003, hlam]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                rcases p1942_3 (m.d 0 1) (by simp) with h2013 | h2013
                · rcases p1942_3 (m.d 1 2) (by simp) with h2014 | h2014
                  · linarith only [h2014, h9, hlam]
                  · rcases p1942_3 (m.d 1 3) (by simp) with h2016 | h2016
                    · rcases p1942_3 (m.d 1 4) (by simp) with h2017 | h2017
                      · linarith only [h1680, h2017, hlam]
                      · rcases p1942_3 (m.d 1 5) (by simp) with h2019 | h2019
                        · linarith only [h1681, h2019, hlam]
                        · linarith only [h1682, h2019, hlam]
                    · linarith only [h1680, h2016, hlam]
                · linarith only [h2, h2013, hlam]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                rcases p1942_3 (m.d 0 1) (by simp) with h2024 | h2024
                · rcases p1942_3 (m.d 1 2) (by simp) with h2025 | h2025
                  · linarith only [h2025, h9, hlam]
                  · rcases p1942_3 (m.d 1 3) (by simp) with h2027 | h2027
                    · rcases p1942_3 (m.d 1 4) (by simp) with h2028 | h2028
                      · linarith only [h1680, h2028, hlam]
                      · rcases p1942_3 (m.d 1 5) (by simp) with h2030 | h2030
                        · linarith only [h1681, h2030, hlam]
                        · rcases h3bigk with h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h0, h1682, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1942_1, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h0, h1937, h1939, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            rcases p2032_3 (m.d 0 3) (by simp) with h2036 | h2036
                            · rcases p2032_3 (m.d 1 3) (by simp) with h2037 | h2037
                              · linarith only [h1, h2037, hlam]
                              · linarith only [h1680, h2037, hlam]
                            · linarith only [h2036, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            rcases p2032_3 (m.d 0 3) (by simp) with h2041 | h2041
                            · rcases p2032_3 (m.d 1 3) (by simp) with h2042 | h2042
                              · linarith only [h1, h2042, hlam]
                              · linarith only [h1681, h2042, hlam]
                            · linarith only [h2041, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h9, hlam, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h4, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h6, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1680, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1937, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1940, hlam, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h7, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1681, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1938, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                    · linarith only [h1681, h2027, hlam]
                · linarith only [h2024, h3, hlam]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h2, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h1682, h1939, h5, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1942_1]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h1680, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h1682, hlam, p1942_1]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h3, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h0, h1682, h1939, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1942_1]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h1681, hlam, p1942_0]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [h0, h1682, h1939, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1942_1]
              · have p1942_0 := h1942c.1
                have p1942_1 := h1942c.2.1
                have p1942_2 := h1942c.2.2.1
                have p1942_3 := h1942c.2.2.2
                linarith only [hlam, p1942_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2078 | h2078
            · linarith only [h0, h1383, h1939, h2078, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h0, h1383, h1939, h4, h6, h8, hlam, p2080_2]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                rcases p2080_3 (m.d 0 1) (by simp) with h2083 | h2083
                · rcases p2080_3 (m.d 1 2) (by simp) with h2084 | h2084
                  · linarith only [h0, h2084, hlam]
                  · rcases p2080_3 (m.d 1 3) (by simp) with h2086 | h2086
                    · linarith only [h2086, hlam, p2080_0]
                    · rcases p2080_3 (m.d 1 4) (by simp) with h2088 | h2088
                      · linarith only [h2, h2088, hlam]
                      · rcases p2080_3 (m.d 1 5) (by simp) with h2090 | h2090
                        · linarith only [h2090, h3, hlam]
                        · rcases h3bigk with h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h0, h1681, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            rcases p2092_3 (m.d 0 3) (by simp) with h2096 | h2096
                            · rcases p2092_3 (m.d 1 3) (by simp) with h2097 | h2097
                              · linarith only [h1, h2097, hlam]
                              · linarith only [h1680, h2097, hlam]
                            · linarith only [h2096, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            rcases p2092_3 (m.d 0 3) (by simp) with h2101 | h2101
                            · rcases p2092_3 (m.d 1 3) (by simp) with h2102 | h2102
                              · linarith only [h1, h2102, hlam]
                              · linarith only [h1681, h2102, hlam]
                            · linarith only [h2101, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h9, hlam, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2080_1, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2078, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2080_1, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h4, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h0, h4, hlam, p2080_2, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h0, h2078, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h6, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1680, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1937, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h2078, hlam, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h7, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1681, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1938, hlam, p2092_0]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [h1681, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2092_1]
                          · have p2092_0 := h2092c.1
                            have p2092_1 := h2092c.2.1
                            have p2092_2 := h2092c.2.2.1
                            have p2092_3 := h2092c.2.2.2
                            linarith only [hlam, p2092_0]
                · linarith only [h2083, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                rcases p2080_3 (m.d 0 1) (by simp) with h2127 | h2127
                · rcases p2080_3 (m.d 1 2) (by simp) with h2128 | h2128
                  · linarith only [h0, h2128, hlam]
                  · rcases p2080_3 (m.d 1 3) (by simp) with h2130 | h2130
                    · linarith only [h1, h2130, hlam]
                    · linarith only [h1680, h2130, hlam]
                · linarith only [h2127, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                rcases p2080_3 (m.d 0 1) (by simp) with h2134 | h2134
                · rcases p2080_3 (m.d 1 2) (by simp) with h2135 | h2135
                  · linarith only [h0, h2135, hlam]
                  · rcases p2080_3 (m.d 1 3) (by simp) with h2137 | h2137
                    · linarith only [h1, h2137, hlam]
                    · linarith only [h1681, h2137, hlam]
                · linarith only [h2134, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h0, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h9, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h1383, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h1609, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h1, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                rcases p2080_3 (m.d 0 1) (by simp) with h2147 | h2147
                · rcases p2080_3 (m.d 1 2) (by simp) with h2148 | h2148
                  · linarith only [h2148, h9, hlam]
                  · rcases p2080_3 (m.d 1 3) (by simp) with h2150 | h2150
                    · rcases p2080_3 (m.d 1 4) (by simp) with h2151 | h2151
                      · linarith only [h1680, h2151, hlam]
                      · linarith only [h1383, h2151, hlam]
                    · linarith only [h2150, h9, hlam]
                · linarith only [h0, h2147, hlam]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                rcases p2080_3 (m.d 0 1) (by simp) with h2157 | h2157
                · rcases p2080_3 (m.d 1 2) (by simp) with h2158 | h2158
                  · linarith only [h2158, h9, hlam]
                  · rcases p2080_3 (m.d 1 3) (by simp) with h2160 | h2160
                    · rcases p2080_3 (m.d 1 4) (by simp) with h2161 | h2161
                      · linarith only [h1680, h2161, hlam]
                      · rcases p2080_3 (m.d 1 5) (by simp) with h2163 | h2163
                        · linarith only [h1681, h2163, hlam]
                        · linarith only [h1682, h2163, hlam]
                    · linarith only [h1680, h2160, hlam]
                · linarith only [h2, h2157, hlam]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                rcases p2080_3 (m.d 0 1) (by simp) with h2168 | h2168
                · rcases p2080_3 (m.d 1 2) (by simp) with h2169 | h2169
                  · linarith only [h2169, h9, hlam]
                  · rcases p2080_3 (m.d 1 3) (by simp) with h2171 | h2171
                    · rcases p2080_3 (m.d 1 4) (by simp) with h2172 | h2172
                      · linarith only [h1680, h2172, hlam]
                      · rcases p2080_3 (m.d 1 5) (by simp) with h2174 | h2174
                        · linarith only [h1681, h2174, hlam]
                        · rcases h3bigk with h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h0, h1682, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2080_1, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            rcases p2176_3 (m.d 0 3) (by simp) with h2180 | h2180
                            · rcases p2176_3 (m.d 1 3) (by simp) with h2181 | h2181
                              · linarith only [h1, h2181, hlam]
                              · linarith only [h1680, h2181, hlam]
                            · linarith only [h2180, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            rcases p2176_3 (m.d 0 3) (by simp) with h2185 | h2185
                            · rcases p2176_3 (m.d 1 3) (by simp) with h2186 | h2186
                              · linarith only [h1, h2186, hlam]
                              · linarith only [h1681, h2186, hlam]
                            · linarith only [h2185, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h1, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h9, hlam, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h4, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h6, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h1680, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h1937, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h2078, hlam, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h7, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h1681, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h1938, hlam, p2176_0]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2176_1]
                          · have p2176_0 := h2176c.1
                            have p2176_1 := h2176c.2.1
                            have p2176_2 := h2176c.2.2.1
                            have p2176_3 := h2176c.2.2.2
                            linarith only [hlam, p2176_0]
                    · linarith only [h1681, h2171, hlam]
                · linarith only [h2168, h3, hlam]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h2, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h0, h1682, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2080_1]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h1680, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h1682, hlam, p2080_1]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h3, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                rcases p2080_3 (m.d 0 1) (by simp) with h2218 | h2218
                · rcases p2080_3 (m.d 1 2) (by simp) with h2219 | h2219
                  · linarith only [h1609, h2219, hlam]
                  · rcases p2080_3 (m.d 1 3) (by simp) with h2221 | h2221
                    · rcases p2080_3 (m.d 1 4) (by simp) with h2222 | h2222
                      · linarith only [h1682, h2222, hlam]
                      · linarith only [h1383, h2222, hlam]
                    · linarith only [h2221, h9, hlam]
                · linarith only [h0, h2218, hlam]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [h1681, hlam, p2080_0]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                rcases p2080_3 (m.d 0 1) (by simp) with h2228 | h2228
                · rcases p2080_3 (m.d 1 2) (by simp) with h2229 | h2229
                  · linarith only [h1609, h2229, hlam]
                  · rcases p2080_3 (m.d 1 3) (by simp) with h2231 | h2231
                    · rcases p2080_3 (m.d 1 4) (by simp) with h2232 | h2232
                      · linarith only [h1682, h2232, hlam]
                      · rcases p2080_3 (m.d 1 5) (by simp) with h2234 | h2234
                        · rcases h3bigk with h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c | h2235c
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h0, h1681, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            rcases p2235_3 (m.d 0 3) (by simp) with h2239 | h2239
                            · rcases p2235_3 (m.d 1 3) (by simp) with h2240 | h2240
                              · linarith only [h1, h2240, hlam]
                              · linarith only [h1680, h2240, hlam]
                            · linarith only [h2239, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            rcases p2235_3 (m.d 0 3) (by simp) with h2244 | h2244
                            · rcases p2235_3 (m.d 1 3) (by simp) with h2245 | h2245
                              · linarith only [h1, h2245, hlam]
                              · linarith only [h1681, h2245, hlam]
                            · linarith only [h2244, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h1, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h9, hlam, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h0, h2078, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h4, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h0, h2078, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h6, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h1680, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h1937, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h2078, hlam, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h7, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h1681, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h1938, hlam, p2235_0]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2235_1]
                          · have p2235_0 := h2235c.1
                            have p2235_1 := h2235c.2.1
                            have p2235_2 := h2235c.2.2.1
                            have p2235_3 := h2235c.2.2.2
                            linarith only [hlam, p2235_0]
                        · linarith only [h1682, h2234, hlam]
                    · linarith only [h1680, h2231, hlam]
                · linarith only [h2, h2228, hlam]
              · have p2080_0 := h2080c.1
                have p2080_1 := h2080c.2.1
                have p2080_2 := h2080c.2.2.1
                have p2080_3 := h2080c.2.2.2
                linarith only [hlam, p2080_0]
        · linarith only [h1, h1681, h1938, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · linarith only [h1680, h1937, h9, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2275 | h2275
    · linarith only [h1680, h1681, h2275, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2277 | h2277
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2278 | h2278
        · linarith only [h0, h1680, h1681, h2278, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2280 | h2280
          · linarith only [h0, h2275, h2277, h2278, h2280, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2282 | h2282
            · linarith only [h1383, h1680, h2280, h2282, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h0, h1383, h2277, h2278, h2282, h4, h6, h8, hlam, p2284_2]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                rcases p2284_3 (m.d 0 1) (by simp) with h2287 | h2287
                · rcases p2284_3 (m.d 1 2) (by simp) with h2288 | h2288
                  · linarith only [h0, h2288, hlam]
                  · rcases p2284_3 (m.d 1 3) (by simp) with h2290 | h2290
                    · linarith only [h2290, hlam, p2284_0]
                    · rcases p2284_3 (m.d 1 4) (by simp) with h2292 | h2292
                      · linarith only [h2, h2292, hlam]
                      · rcases p2284_3 (m.d 1 5) (by simp) with h2294 | h2294
                        · linarith only [h2294, h3, hlam]
                        · linarith only [h1681, h2294, hlam]
                · linarith only [h2287, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                rcases p2284_3 (m.d 0 1) (by simp) with h2298 | h2298
                · rcases p2284_3 (m.d 1 2) (by simp) with h2299 | h2299
                  · linarith only [h0, h2299, hlam]
                  · rcases p2284_3 (m.d 1 3) (by simp) with h2301 | h2301
                    · linarith only [h1, h2301, hlam]
                    · linarith only [h1680, h2301, hlam]
                · linarith only [h2298, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                rcases p2284_3 (m.d 0 1) (by simp) with h2305 | h2305
                · rcases p2284_3 (m.d 1 2) (by simp) with h2306 | h2306
                  · linarith only [h0, h2306, hlam]
                  · rcases p2284_3 (m.d 1 3) (by simp) with h2308 | h2308
                    · linarith only [h1, h2308, hlam]
                    · rcases p2284_3 (m.d 1 4) (by simp) with h2310 | h2310
                      · linarith only [h2, h2310, hlam]
                      · rcases p2284_3 (m.d 1 5) (by simp) with h2312 | h2312
                        · linarith only [h2312, hlam, p2284_0]
                        · rcases h3bigk with h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h1680, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h1383, h2277, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            rcases p2314_3 (m.d 0 3) (by simp) with h2318 | h2318
                            · rcases p2314_3 (m.d 1 3) (by simp) with h2319 | h2319
                              · linarith only [h1, h2319, hlam]
                              · linarith only [h1680, h2319, hlam]
                            · linarith only [h2318, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h1609, h2278, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h1, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h9, hlam, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h1681, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h4, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2278, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h6, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h1680, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2277, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2282, hlam, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h7, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h1680, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h2282, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                · linarith only [h2305, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h0, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h9, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h1383, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h1609, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h1, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h0, h2278, h2282, h4, h6, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2284_1]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h0, h2278, h2282, h4, h6, h8, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2284_1]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h1681, hlam, p2284_1]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h2, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h0, h1383, h2277, h2278, h2282, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2284_1]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h1680, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h2275, hlam, p2284_1]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h3, hlam, p2284_0]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                rcases p2284_3 (m.d 0 1) (by simp) with h2361 | h2361
                · rcases p2284_3 (m.d 1 2) (by simp) with h2362 | h2362
                  · linarith only [h1609, h2362, hlam]
                  · rcases p2284_3 (m.d 1 3) (by simp) with h2364 | h2364
                    · linarith only [h1681, h2364, hlam]
                    · linarith only [h2364, h9, hlam]
                · linarith only [h0, h2361, hlam]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [h1680, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2284_1]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                rcases p2284_3 (m.d 0 1) (by simp) with h2369 | h2369
                · rcases p2284_3 (m.d 1 2) (by simp) with h2370 | h2370
                  · linarith only [h1609, h2370, hlam]
                  · rcases p2284_3 (m.d 1 3) (by simp) with h2372 | h2372
                    · linarith only [h1681, h2372, hlam]
                    · linarith only [h1680, h2372, hlam]
                · linarith only [h2, h2369, hlam]
              · have p2284_0 := h2284c.1
                have p2284_1 := h2284c.2.1
                have p2284_2 := h2284c.2.2.1
                have p2284_3 := h2284c.2.2.2
                linarith only [hlam, p2284_0]
      · linarith only [h1, h1680, h2277, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

end R2N4
