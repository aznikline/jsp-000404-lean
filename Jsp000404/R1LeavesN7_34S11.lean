import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h1705 | h1705
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1706 | h1706
    · linarith only [h10, h1706, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1708 | h1708
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1709 | h1709
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1710 | h1710
          · linarith only [h0, h1706, h1708, h1710, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1712 | h1712
            · linarith only [h0, h10, h1712, h5, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h1708, h1710, h1712, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h10, h1708, h1709, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1716 | h1716
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1717 | h1717
          · linarith only [h0, h10, h1717, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1719 | h1719
            · linarith only [h1708, h1719, h9, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1721 | h1721
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1722 | h1722
                · rcases h1bigk with h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    rcases p1723_3 (m.d 0 1) (by simp) with h1725 | h1725
                    · rcases p1723_3 (m.d 1 2) (by simp) with h1726 | h1726
                      · linarith only [h1726, hlam, p1723_0]
                      · rcases p1723_3 (m.d 1 3) (by simp) with h1728 | h1728
                        · linarith only [h1, h1728, hlam]
                        · rcases p1723_3 (m.d 1 4) (by simp) with h1730 | h1730
                          · linarith only [h1730, h2, hlam]
                          · linarith only [h10, h1730, hlam]
                    · linarith only [h1725, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    rcases p1723_3 (m.d 0 1) (by simp) with h1734 | h1734
                    · rcases p1723_3 (m.d 1 2) (by simp) with h1735 | h1735
                      · linarith only [h0, h1735, hlam]
                      · linarith only [h1735, h9, hlam]
                    · linarith only [h1734, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    rcases p1723_3 (m.d 0 1) (by simp) with h1739 | h1739
                    · rcases p1723_3 (m.d 1 2) (by simp) with h1740 | h1740
                      · linarith only [h0, h1740, hlam]
                      · rcases p1723_3 (m.d 1 3) (by simp) with h1742 | h1742
                        · linarith only [h1, h1742, hlam]
                        · rcases p1723_3 (m.d 1 4) (by simp) with h1744 | h1744
                          · linarith only [h1744, hlam, p1723_0]
                          · rcases p1723_3 (m.d 1 5) (by simp) with h1746 | h1746
                            · linarith only [h1746, h3, hlam]
                            · rcases h3bigk with h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                rcases p1748_3 (m.d 0 3) (by simp) with h1750 | h1750
                                · rcases p1748_3 (m.d 1 3) (by simp) with h1751 | h1751
                                  · linarith only [h1, h1751, hlam]
                                  · rcases p1748_3 (m.d 2 3) (by simp) with h1753 | h1753
                                    · linarith only [h1753, h4, hlam]
                                    · rcases p1748_3 (m.d 3 4) (by simp) with h1755 | h1755
                                      · linarith only [h1755, h6, hlam]
                                      · linarith only [h1706, h1755, hlam]
                                · linarith only [h1, h1750, hlam]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h10, h1705, h1717, h1719, h6, hlam, p1748_2]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h10, h1705, h1717, h1719, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1748_1]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                rcases p1748_3 (m.d 0 3) (by simp) with h1761 | h1761
                                · rcases p1748_3 (m.d 1 3) (by simp) with h1762 | h1762
                                  · linarith only [h1, h1762, hlam]
                                  · rcases p1748_3 (m.d 2 3) (by simp) with h1764 | h1764
                                    · linarith only [h1764, h4, hlam]
                                    · rcases p1748_3 (m.d 3 4) (by simp) with h1766 | h1766
                                      · linarith only [h1766, h6, hlam]
                                      · linarith only [h1722, h1766, hlam]
                                · linarith only [h1761, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h1, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h1708, hc23, hc35, hlam, hphi, p1748_1]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h1706, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h1708, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h4, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h9, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h1717, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h1719, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h6, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                rcases p1748_3 (m.d 0 3) (by simp) with h1781 | h1781
                                · rcases p1748_3 (m.d 1 3) (by simp) with h1782 | h1782
                                  · linarith only [h1782, hlam, p1748_0]
                                  · rcases p1748_3 (m.d 2 3) (by simp) with h1784 | h1784
                                    · linarith only [h1717, h1784, hlam]
                                    · rcases p1748_3 (m.d 3 4) (by simp) with h1786 | h1786
                                      · rcases p1748_3 (m.d 3 5) (by simp) with h1787 | h1787
                                        · linarith only [h1722, h1787, hlam]
                                        · linarith only [h1708, h1787, hlam]
                                      · linarith only [h1786, hlam, p1748_0]
                                · linarith only [h1, h1781, hlam]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                rcases p1748_3 (m.d 0 3) (by simp) with h1792 | h1792
                                · rcases p1748_3 (m.d 1 3) (by simp) with h1793 | h1793
                                  · linarith only [h1706, h1793, hlam]
                                  · linarith only [h1793, h9, hlam]
                                · linarith only [h1792, h4, hlam]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h0, h1708, h4, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1748_1]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h7, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                rcases p1748_3 (m.d 0 3) (by simp) with h1800 | h1800
                                · rcases p1748_3 (m.d 1 3) (by simp) with h1801 | h1801
                                  · linarith only [h1801, hlam, p1748_0]
                                  · rcases p1748_3 (m.d 2 3) (by simp) with h1803 | h1803
                                    · linarith only [h1719, h1803, hlam]
                                    · rcases p1748_3 (m.d 3 4) (by simp) with h1805 | h1805
                                      · rcases p1748_3 (m.d 3 5) (by simp) with h1806 | h1806
                                        · rcases h4bigk with h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            rcases p1807_3 (m.d 0 4) (by simp) with h1809 | h1809
                                            · rcases p1807_3 (m.d 1 4) (by simp) with h1810 | h1810
                                              · linarith only [h1810, h2, hlam]
                                              · rcases p1807_3 (m.d 2 4) (by simp) with h1812 | h1812
                                                · linarith only [h1812, h5, hlam]
                                                · linarith only [h10, h1812, hlam]
                                            · linarith only [h1809, h2, hlam]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h0, h10, h1705, h1719, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h0, h10, h1705, h1717, h1719, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            rcases p1807_3 (m.d 0 4) (by simp) with h1818 | h1818
                                            · rcases p1807_3 (m.d 1 4) (by simp) with h1819 | h1819
                                              · linarith only [h1819, h2, hlam]
                                              · linarith only [h1716, h1819, hlam]
                                            · linarith only [h1818, hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h2, hlam, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h10, hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h1706, hlam, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p1723_1, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h5, hlam, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h0, h5, hlam, p1723_2, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h1717, hlam, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            rcases p1807_3 (m.d 0 4) (by simp) with h1832 | h1832
                                            · rcases p1807_3 (m.d 1 4) (by simp) with h1833 | h1833
                                              · linarith only [h10, h1833, hlam]
                                              · linarith only [h1716, h1833, hlam]
                                            · linarith only [h1832, h8, hlam]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h6, hlam, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h0, h10, h1705, h1719, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h0, h10, h1705, h1719, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1807_1]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            rcases p1807_3 (m.d 0 4) (by simp) with h1841 | h1841
                                            · rcases p1807_3 (m.d 1 4) (by simp) with h1842 | h1842
                                              · linarith only [h1706, h1842, hlam]
                                              · linarith only [h1716, h1842, hlam]
                                            · linarith only [h1841, h8, hlam]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h8, hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h1716, hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h1721, hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [h1722, hlam, p1807_0]
                                          · have p1807_0 := h1807c.1
                                            have p1807_1 := h1807c.2.1
                                            have p1807_2 := h1807c.2.2.1
                                            have p1807_3 := h1807c.2.2.2
                                            linarith only [hlam, p1807_0]
                                        · linarith only [h1806, hlam, p1748_0]
                                      · linarith only [h1706, h1805, hlam]
                                · linarith only [h1, h1800, hlam]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                rcases p1748_3 (m.d 0 3) (by simp) with h1854 | h1854
                                · rcases p1748_3 (m.d 1 3) (by simp) with h1855 | h1855
                                  · linarith only [h1708, h1855, hlam]
                                  · linarith only [h1855, h9, hlam]
                                · linarith only [h1854, h4, hlam]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [h1722, hlam, p1748_0]
                              · have p1748_0 := h1748c.1
                                have p1748_1 := h1748c.2.1
                                have p1748_2 := h1748c.2.2.1
                                have p1748_3 := h1748c.2.2.2
                                linarith only [hlam, p1748_0]
                    · linarith only [h1739, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    rcases p1723_3 (m.d 0 1) (by simp) with h1862 | h1862
                    · rcases p1723_3 (m.d 1 2) (by simp) with h1863 | h1863
                      · linarith only [h0, h1863, hlam]
                      · linarith only [h1705, h1863, hlam]
                    · linarith only [h1862, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h0, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h0, h10, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1723_1]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h10, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h0, h10, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p1723_1]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h1, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h9, hlam, p1723_1]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h1706, hlam, p1723_1]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h1708, hlam, p1723_1]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h2, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1723_1]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    rcases p1723_3 (m.d 0 1) (by simp) with h1879 | h1879
                    · rcases p1723_3 (m.d 1 2) (by simp) with h1880 | h1880
                      · linarith only [h10, h1880, hlam]
                      · linarith only [h1880, h9, hlam]
                    · linarith only [h1, h1879, hlam]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    rcases p1723_3 (m.d 0 1) (by simp) with h1885 | h1885
                    · rcases p1723_3 (m.d 1 2) (by simp) with h1886 | h1886
                      · linarith only [h10, h1886, hlam]
                      · linarith only [h1705, h1886, hlam]
                    · linarith only [h1885, h3, hlam]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h3, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h1705, hlam, p1723_1]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h0, h10, h1705, h1717, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1723_1]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [h1716, hlam, p1723_0]
                  · have p1723_0 := h1723c.1
                    have p1723_1 := h1723c.2.1
                    have p1723_2 := h1723c.2.2.1
                    have p1723_3 := h1723c.2.2.2
                    linarith only [hlam, p1723_0]
                · linarith only [h0, h10, h1717, h1722, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h10, h1705, h1719, h1721, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h10, h1705, h1716, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1898 | h1898
    · linarith only [h10, h1898, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1900 | h1900
      · linarith only [h1705, h1900, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1902 | h1902
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1903 | h1903
          · linarith only [h10, h1898, h1903, h9, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1905 | h1905
            · linarith only [h1705, h1900, h1905, h9, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1907 | h1907
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1908 | h1908
                · rcases h1bigk with h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c | h1909c
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    rcases p1909_3 (m.d 0 1) (by simp) with h1911 | h1911
                    · rcases p1909_3 (m.d 1 2) (by simp) with h1912 | h1912
                      · linarith only [h1912, hlam, p1909_0]
                      · rcases p1909_3 (m.d 1 3) (by simp) with h1914 | h1914
                        · linarith only [h1, h1914, hlam]
                        · rcases p1909_3 (m.d 1 4) (by simp) with h1916 | h1916
                          · linarith only [h1916, h2, hlam]
                          · linarith only [h10, h1916, hlam]
                    · linarith only [h1911, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    rcases p1909_3 (m.d 0 1) (by simp) with h1920 | h1920
                    · rcases p1909_3 (m.d 1 2) (by simp) with h1921 | h1921
                      · linarith only [h0, h1921, hlam]
                      · linarith only [h1921, h9, hlam]
                    · linarith only [h1920, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    rcases p1909_3 (m.d 0 1) (by simp) with h1925 | h1925
                    · rcases p1909_3 (m.d 1 2) (by simp) with h1926 | h1926
                      · linarith only [h0, h1926, hlam]
                      · rcases p1909_3 (m.d 1 3) (by simp) with h1928 | h1928
                        · linarith only [h1, h1928, hlam]
                        · rcases p1909_3 (m.d 1 4) (by simp) with h1930 | h1930
                          · linarith only [h1930, hlam, p1909_0]
                          · rcases p1909_3 (m.d 1 5) (by simp) with h1932 | h1932
                            · linarith only [h1932, h3, hlam]
                            · rcases h3bigk with h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                rcases p1934_3 (m.d 0 3) (by simp) with h1936 | h1936
                                · rcases p1934_3 (m.d 1 3) (by simp) with h1937 | h1937
                                  · linarith only [h1, h1937, hlam]
                                  · rcases p1934_3 (m.d 2 3) (by simp) with h1939 | h1939
                                    · linarith only [h1939, h4, hlam]
                                    · rcases p1934_3 (m.d 3 4) (by simp) with h1941 | h1941
                                      · linarith only [h1941, h6, hlam]
                                      · linarith only [h1898, h1941, hlam]
                                · linarith only [h1, h1936, hlam]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h1705, h1903, h1907, h6, h9, hlam, p1934_2]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h0, h1705, h1903, h1907, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1934_1]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h0, h1705, h1905, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1934_1]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h1, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h1705, h1903, h1907, h9, hc23, hc34, hlam, hphi, p1934_1]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h1898, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h1900, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h4, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h9, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h1903, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h1905, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h6, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                rcases p1934_3 (m.d 0 3) (by simp) with h1959 | h1959
                                · rcases p1934_3 (m.d 1 3) (by simp) with h1960 | h1960
                                  · linarith only [h1960, hlam, p1934_0]
                                  · rcases p1934_3 (m.d 2 3) (by simp) with h1962 | h1962
                                    · linarith only [h1903, h1962, hlam]
                                    · rcases p1934_3 (m.d 3 4) (by simp) with h1964 | h1964
                                      · rcases p1934_3 (m.d 3 5) (by simp) with h1965 | h1965
                                        · linarith only [h1908, h1965, hlam]
                                        · linarith only [h1900, h1965, hlam]
                                      · linarith only [h1964, hlam, p1934_0]
                                · linarith only [h1, h1959, hlam]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                rcases p1934_3 (m.d 0 3) (by simp) with h1970 | h1970
                                · rcases p1934_3 (m.d 1 3) (by simp) with h1971 | h1971
                                  · linarith only [h1898, h1971, hlam]
                                  · linarith only [h1971, h9, hlam]
                                · linarith only [h1970, h4, hlam]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h0, h1900, h4, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1934_1]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h7, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                rcases p1934_3 (m.d 0 3) (by simp) with h1978 | h1978
                                · rcases p1934_3 (m.d 1 3) (by simp) with h1979 | h1979
                                  · linarith only [h1979, hlam, p1934_0]
                                  · rcases p1934_3 (m.d 2 3) (by simp) with h1981 | h1981
                                    · linarith only [h1905, h1981, hlam]
                                    · rcases p1934_3 (m.d 3 4) (by simp) with h1983 | h1983
                                      · rcases p1934_3 (m.d 3 5) (by simp) with h1984 | h1984
                                        · rcases h4bigk with h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            rcases p1985_3 (m.d 0 4) (by simp) with h1987 | h1987
                                            · rcases p1985_3 (m.d 1 4) (by simp) with h1988 | h1988
                                              · linarith only [h1988, h2, hlam]
                                              · rcases p1985_3 (m.d 2 4) (by simp) with h1990 | h1990
                                                · linarith only [h1990, h5, hlam]
                                                · linarith only [h10, h1990, hlam]
                                            · linarith only [h1987, h2, hlam]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h0, h10, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h0, h1705, h1903, h1907, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            rcases p1985_3 (m.d 0 4) (by simp) with h1996 | h1996
                                            · rcases p1985_3 (m.d 1 4) (by simp) with h1997 | h1997
                                              · linarith only [h1997, h2, hlam]
                                              · linarith only [h1902, h1997, hlam]
                                            · linarith only [h1996, hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h2, hlam, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h10, hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h1898, hlam, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p1909_1, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h5, hlam, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h0, h5, hlam, p1909_2, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h1903, hlam, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            rcases p1985_3 (m.d 0 4) (by simp) with h2010 | h2010
                                            · rcases p1985_3 (m.d 1 4) (by simp) with h2011 | h2011
                                              · linarith only [h10, h2011, hlam]
                                              · linarith only [h1902, h2011, hlam]
                                            · linarith only [h2010, h8, hlam]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h6, hlam, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h0, h1705, h1902, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h0, h1705, h1907, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1985_1]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            rcases p1985_3 (m.d 0 4) (by simp) with h2019 | h2019
                                            · rcases p1985_3 (m.d 1 4) (by simp) with h2020 | h2020
                                              · linarith only [h1898, h2020, hlam]
                                              · linarith only [h1902, h2020, hlam]
                                            · linarith only [h2019, h8, hlam]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h8, hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h1902, hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h1907, hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [h1908, hlam, p1985_0]
                                          · have p1985_0 := h1985c.1
                                            have p1985_1 := h1985c.2.1
                                            have p1985_2 := h1985c.2.2.1
                                            have p1985_3 := h1985c.2.2.2
                                            linarith only [hlam, p1985_0]
                                        · linarith only [h1984, hlam, p1934_0]
                                      · linarith only [h1898, h1983, hlam]
                                · linarith only [h1, h1978, hlam]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                rcases p1934_3 (m.d 0 3) (by simp) with h2032 | h2032
                                · rcases p1934_3 (m.d 1 3) (by simp) with h2033 | h2033
                                  · linarith only [h1900, h2033, hlam]
                                  · linarith only [h2033, h9, hlam]
                                · linarith only [h2032, h4, hlam]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [h1908, hlam, p1934_0]
                              · have p1934_0 := h1934c.1
                                have p1934_1 := h1934c.2.1
                                have p1934_2 := h1934c.2.2.1
                                have p1934_3 := h1934c.2.2.2
                                linarith only [hlam, p1934_0]
                    · linarith only [h1925, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    rcases p1909_3 (m.d 0 1) (by simp) with h2040 | h2040
                    · rcases p1909_3 (m.d 1 2) (by simp) with h2041 | h2041
                      · linarith only [h0, h2041, hlam]
                      · rcases p1909_3 (m.d 1 3) (by simp) with h2043 | h2043
                        · linarith only [h1, h2043, hlam]
                        · rcases p1909_3 (m.d 1 4) (by simp) with h2045 | h2045
                          · linarith only [h2, h2045, hlam]
                          · linarith only [h1902, h2045, hlam]
                    · linarith only [h2040, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h0, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h1705, h1905, h9, hc23, hc35, hlam, hphi, p1909_1]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h10, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h1705, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h1, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h9, hlam, p1909_1]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h1898, hlam, p1909_1]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h1900, hlam, p1909_1]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h2, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1909_1]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    rcases p1909_3 (m.d 0 1) (by simp) with h2061 | h2061
                    · rcases p1909_3 (m.d 1 2) (by simp) with h2062 | h2062
                      · linarith only [h10, h2062, hlam]
                      · linarith only [h2062, h9, hlam]
                    · linarith only [h1, h2061, hlam]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h0, h10, h1705, h1903, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1909_1]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h3, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1909_1]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    rcases p1909_3 (m.d 0 1) (by simp) with h2070 | h2070
                    · rcases p1909_3 (m.d 1 2) (by simp) with h2071 | h2071
                      · linarith only [h1705, h2071, hlam]
                      · linarith only [h2071, h9, hlam]
                    · linarith only [h1, h2070, hlam]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [h1902, hlam, p1909_0]
                  · have p1909_0 := h1909c.1
                    have p1909_1 := h1909c.2.1
                    have p1909_2 := h1909c.2.2.1
                    have p1909_3 := h1909c.2.2.2
                    linarith only [hlam, p1909_0]
                · linarith only [h0, h10, h1903, h1908, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h10, h1902, h1907, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2079 | h2079
          · linarith only [h0, h10, h2079, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2081 | h2081
            · linarith only [h0, h10, h1902, h2081, h4, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2083 | h2083
              · linarith only [h0, h10, h1902, h2079, h2083, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h10, h2083, h9, hc23, hc45, hlam, hphi, ht34]

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (h2086 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h2087 | h2087
  · rcases m.htr 1 3 4 (by decide) (by decide) with h2088 | h2088
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2089 | h2089
      · rcases m.htr 1 4 5 (by decide) (by decide) with h2090 | h2090
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2091 | h2091
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2092 | h2092
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2093 | h2093
              · linarith only [h0, h2086, h2093, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h2086, h2090, h2093, h4, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2087, h2092, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h2087, h2091, h4, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2098 | h2098
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2099 | h2099
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2100 | h2100
              · linarith only [h2086, h2090, h2100, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2102 | h2102
                · linarith only [h0, h2086, h2090, h2098, h2102, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b]
                · rcases h1bigk with h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    rcases p2104_3 (m.d 0 1) (by simp) with h2106 | h2106
                    · rcases p2104_3 (m.d 1 2) (by simp) with h2107 | h2107
                      · linarith only [h2107, hlam, p2104_0]
                      · rcases p2104_3 (m.d 1 3) (by simp) with h2109 | h2109
                        · linarith only [h1, h2109, hlam]
                        · linarith only [h2109, h9, hlam]
                    · linarith only [h2106, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    rcases p2104_3 (m.d 0 1) (by simp) with h2113 | h2113
                    · rcases p2104_3 (m.d 1 2) (by simp) with h2114 | h2114
                      · linarith only [h0, h2114, hlam]
                      · rcases p2104_3 (m.d 1 3) (by simp) with h2116 | h2116
                        · linarith only [h2116, hlam, p2104_0]
                        · rcases p2104_3 (m.d 1 4) (by simp) with h2118 | h2118
                          · linarith only [h2, h2118, hlam]
                          · rcases p2104_3 (m.d 1 5) (by simp) with h2120 | h2120
                            · linarith only [h2120, h3, hlam]
                            · rcases h3bigk with h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                rcases p2122_3 (m.d 0 3) (by simp) with h2124 | h2124
                                · rcases p2122_3 (m.d 1 3) (by simp) with h2125 | h2125
                                  · linarith only [h1, h2125, hlam]
                                  · rcases p2122_3 (m.d 2 3) (by simp) with h2127 | h2127
                                    · linarith only [h2127, h4, hlam]
                                    · linarith only [h2127, h9, hlam]
                                · linarith only [h1, h2124, hlam]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h0, h2087, h2100, h4, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2122_1]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                rcases p2122_3 (m.d 0 3) (by simp) with h2132 | h2132
                                · rcases p2122_3 (m.d 1 3) (by simp) with h2133 | h2133
                                  · linarith only [h1, h2133, hlam]
                                  · linarith only [h2088, h2133, hlam]
                                · linarith only [h2132, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                rcases p2122_3 (m.d 0 3) (by simp) with h2137 | h2137
                                · rcases p2122_3 (m.d 1 3) (by simp) with h2138 | h2138
                                  · linarith only [h1, h2138, hlam]
                                  · linarith only [h2089, h2138, hlam]
                                · linarith only [h2137, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h1, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h9, hlam, p2122_1]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2104_1, p2122_1]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h2102, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2104_1, p2122_1]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h4, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h0, h4, hlam, p2104_2, p2122_1]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                rcases p2122_3 (m.d 0 3) (by simp) with h2150 | h2150
                                · rcases p2122_3 (m.d 1 3) (by simp) with h2151 | h2151
                                  · linarith only [h2151, h9, hlam]
                                  · linarith only [h2088, h2151, hlam]
                                · linarith only [h2150, h6, hlam]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                rcases p2122_3 (m.d 0 3) (by simp) with h2155 | h2155
                                · rcases p2122_3 (m.d 1 3) (by simp) with h2156 | h2156
                                  · linarith only [h2156, h9, hlam]
                                  · linarith only [h2089, h2156, hlam]
                                · linarith only [h2155, h7, hlam]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h6, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h2088, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h2098, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h2102, hlam, p2122_1]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h7, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h2089, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h2099, hlam, p2122_0]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [h2089, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2104_1, p2122_1]
                              · have p2122_0 := h2122c.1
                                have p2122_1 := h2122c.2.1
                                have p2122_2 := h2122c.2.2.1
                                have p2122_3 := h2122c.2.2.2
                                linarith only [hlam, p2122_0]
                    · linarith only [h2113, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    rcases p2104_3 (m.d 0 1) (by simp) with h2171 | h2171
                    · rcases p2104_3 (m.d 1 2) (by simp) with h2172 | h2172
                      · linarith only [h0, h2172, hlam]
                      · linarith only [h2086, h2172, hlam]
                    · linarith only [h2171, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    rcases p2104_3 (m.d 0 1) (by simp) with h2176 | h2176
                    · rcases p2104_3 (m.d 1 2) (by simp) with h2177 | h2177
                      · linarith only [h0, h2177, hlam]
                      · linarith only [h2087, h2177, hlam]
                    · linarith only [h2176, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h0, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h9, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h0, h4, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2104_1]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p2104_1]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h1, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h0, h2087, h2100, h4, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2104_1]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    rcases p2104_3 (m.d 0 1) (by simp) with h2189 | h2189
                    · rcases p2104_3 (m.d 1 2) (by simp) with h2190 | h2190
                      · linarith only [h2190, h9, hlam]
                      · linarith only [h2086, h2190, hlam]
                    · linarith only [h2, h2189, hlam]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    rcases p2104_3 (m.d 0 1) (by simp) with h2194 | h2194
                    · rcases p2104_3 (m.d 1 2) (by simp) with h2195 | h2195
                      · linarith only [h2195, h9, hlam]
                      · linarith only [h2087, h2195, hlam]
                    · linarith only [h2194, h3, hlam]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h2, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h2086, hlam, p2104_1]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h2088, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h2090, hlam, p2104_1]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h3, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h2087, hlam, p2104_1]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h2089, hlam, p2104_0]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [h0, h2086, h2087, h2098, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2104_1]
                  · have p2104_0 := h2104c.1
                    have p2104_1 := h2104c.2.1
                    have p2104_2 := h2104c.2.2.1
                    have p2104_3 := h2104c.2.2.2
                    linarith only [hlam, p2104_0]
            · linarith only [h0, h2086, h2098, h2099, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h2086, h2098, h4, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h2087, h2089, h9, hlam]
    · linarith only [h2086, h2088, h9, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h2213 | h2213
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2214 | h2214
      · rcases m.htr 1 4 5 (by decide) (by decide) with h2215 | h2215
        · linarith only [h2086, h2087, h2215, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2217 | h2217
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2218 | h2218
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2219 | h2219
              · linarith only [h2086, h2087, h2215, h2218, h2219, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2221 | h2221
                · linarith only [h2086, h2087, h2217, h2219, h2221, hlam]
                · rcases h1bigk with h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    rcases p2223_3 (m.d 0 1) (by simp) with h2225 | h2225
                    · rcases p2223_3 (m.d 1 2) (by simp) with h2226 | h2226
                      · linarith only [h2226, hlam, p2223_0]
                      · rcases p2223_3 (m.d 1 3) (by simp) with h2228 | h2228
                        · linarith only [h1, h2228, hlam]
                        · linarith only [h2228, h9, hlam]
                    · linarith only [h2225, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    rcases p2223_3 (m.d 0 1) (by simp) with h2232 | h2232
                    · rcases p2223_3 (m.d 1 2) (by simp) with h2233 | h2233
                      · linarith only [h0, h2233, hlam]
                      · rcases p2223_3 (m.d 1 3) (by simp) with h2235 | h2235
                        · linarith only [h2235, hlam, p2223_0]
                        · rcases p2223_3 (m.d 1 4) (by simp) with h2237 | h2237
                          · linarith only [h2, h2237, hlam]
                          · rcases p2223_3 (m.d 1 5) (by simp) with h2239 | h2239
                            · linarith only [h2239, h3, hlam]
                            · rcases h3bigk with h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                rcases p2241_3 (m.d 0 3) (by simp) with h2243 | h2243
                                · rcases p2241_3 (m.d 1 3) (by simp) with h2244 | h2244
                                  · linarith only [h1, h2244, hlam]
                                  · rcases p2241_3 (m.d 2 3) (by simp) with h2246 | h2246
                                    · linarith only [h2246, h4, hlam]
                                    · linarith only [h2246, h9, hlam]
                                · linarith only [h1, h2243, hlam]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h0, h2086, h2217, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2241_1]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h2086, h2087, h2217, h2219, h6, h8, hlam, p2241_2]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                rcases p2241_3 (m.d 0 3) (by simp) with h2252 | h2252
                                · rcases p2241_3 (m.d 1 3) (by simp) with h2253 | h2253
                                  · linarith only [h1, h2253, hlam]
                                  · linarith only [h2214, h2253, hlam]
                                · linarith only [h2252, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h1, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h9, hlam, p2241_1]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2223_1, p2241_1]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p2223_1, p2241_1]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h4, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h0, h4, hlam, p2223_2, p2241_1]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                rcases p2241_3 (m.d 0 3) (by simp) with h2265 | h2265
                                · rcases p2241_3 (m.d 1 3) (by simp) with h2266 | h2266
                                  · linarith only [h2266, h9, hlam]
                                  · linarith only [h2213, h2266, hlam]
                                · linarith only [h2265, h6, hlam]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                rcases p2241_3 (m.d 0 3) (by simp) with h2270 | h2270
                                · rcases p2241_3 (m.d 1 3) (by simp) with h2271 | h2271
                                  · linarith only [h2271, h9, hlam]
                                  · linarith only [h2214, h2271, hlam]
                                · linarith only [h2270, h7, hlam]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h6, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h2213, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h2217, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h2221, hlam, p2241_1]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h7, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h2214, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h2218, hlam, p2241_0]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [h2214, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2223_1, p2241_1]
                              · have p2241_0 := h2241c.1
                                have p2241_1 := h2241c.2.1
                                have p2241_2 := h2241c.2.2.1
                                have p2241_3 := h2241c.2.2.2
                                linarith only [hlam, p2241_0]
                    · linarith only [h2232, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    rcases p2223_3 (m.d 0 1) (by simp) with h2286 | h2286
                    · rcases p2223_3 (m.d 1 2) (by simp) with h2287 | h2287
                      · linarith only [h0, h2287, hlam]
                      · linarith only [h2086, h2287, hlam]
                    · linarith only [h2286, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    rcases p2223_3 (m.d 0 1) (by simp) with h2291 | h2291
                    · rcases p2223_3 (m.d 1 2) (by simp) with h2292 | h2292
                      · linarith only [h0, h2292, hlam]
                      · rcases p2223_3 (m.d 1 3) (by simp) with h2294 | h2294
                        · linarith only [h1, h2294, hlam]
                        · linarith only [h2214, h2294, hlam]
                    · linarith only [h2291, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h0, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h9, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h0, h2087, h2219, h4, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2223_1]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h2087, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h1, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h0, h2086, h4, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2223_1]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    rcases p2223_3 (m.d 0 1) (by simp) with h2306 | h2306
                    · rcases p2223_3 (m.d 1 2) (by simp) with h2307 | h2307
                      · linarith only [h2307, h9, hlam]
                      · linarith only [h2086, h2307, hlam]
                    · linarith only [h2, h2306, hlam]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h0, h2086, h2087, h2217, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2223_1]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h2, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h2086, hlam, p2223_1]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h2213, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h2215, hlam, p2223_1]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h3, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h2086, h2217, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2223_1]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [h2214, hlam, p2223_0]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    rcases p2223_3 (m.d 0 1) (by simp) with h2320 | h2320
                    · rcases p2223_3 (m.d 1 2) (by simp) with h2321 | h2321
                      · linarith only [h2087, h2321, hlam]
                      · linarith only [h2086, h2321, hlam]
                    · linarith only [h2, h2320, hlam]
                  · have p2223_0 := h2223c.1
                    have p2223_1 := h2223c.2.1
                    have p2223_2 := h2223c.2.2.1
                    have p2223_3 := h2223c.2.2.2
                    linarith only [hlam, p2223_0]
            · linarith only [h2214, h2218, h9, hlam]
          · linarith only [h0, h2086, h2217, h4, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h2328 | h2328
        · linarith only [h2086, h2087, h2328, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2330 | h2330
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2331 | h2331
            · linarith only [h0, h2086, h2214, h2331, h4, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2086, h2330, h2331, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h2086, h2330, h4, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h2086, h2213, h9, hlam]

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2336 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h2337 | h2337
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2338 | h2338
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2339 | h2339
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2340 | h2340
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2341 | h2341
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2342 | h2342
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2343 | h2343
              · rcases h1bigk with h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  rcases p2344_3 (m.d 0 1) (by simp) with h2346 | h2346
                  · rcases p2344_3 (m.d 1 2) (by simp) with h2347 | h2347
                    · linarith only [h2347, hlam, p2344_0]
                    · rcases p2344_3 (m.d 1 3) (by simp) with h2349 | h2349
                      · linarith only [h1, h2349, hlam]
                      · linarith only [h2349, h9, hlam]
                  · linarith only [h2346, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h2337, h2343, hc01, hc45, hlam, hphi, ht0b, ht5b, p2344_1]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  rcases p2344_3 (m.d 0 1) (by simp) with h2354 | h2354
                  · rcases p2344_3 (m.d 1 2) (by simp) with h2355 | h2355
                    · linarith only [h0, h2355, hlam]
                    · rcases p2344_3 (m.d 1 3) (by simp) with h2357 | h2357
                      · linarith only [h1, h2357, hlam]
                      · linarith only [h2337, h2357, hlam]
                  · linarith only [h2354, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  rcases p2344_3 (m.d 0 1) (by simp) with h2361 | h2361
                  · rcases p2344_3 (m.d 1 2) (by simp) with h2362 | h2362
                    · linarith only [h0, h2362, hlam]
                    · linarith only [h2336, h2362, hlam]
                  · linarith only [h2361, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h0, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h9, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h2086, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h0, h2086, h2340, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p2344_1]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h1, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h0, h2336, h2341, h2343, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p2344_1]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h0, h2086, h2336, h2341, h2343, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p2344_1]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  rcases p2344_3 (m.d 0 1) (by simp) with h2375 | h2375
                  · rcases p2344_3 (m.d 1 2) (by simp) with h2376 | h2376
                    · linarith only [h2376, h9, hlam]
                    · linarith only [h2336, h2376, hlam]
                  · linarith only [h2375, h3, hlam]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h2, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h2, h2336, h2341, h2343, hc01, hc45, hlam, hphi, ht0b, ht5b, p2344_1]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h2337, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  rcases p2344_3 (m.d 0 1) (by simp) with h2384 | h2384
                  · rcases p2344_3 (m.d 1 2) (by simp) with h2385 | h2385
                    · linarith only [h2086, h2385, hlam]
                    · linarith only [h2336, h2385, hlam]
                  · linarith only [h2384, h3, hlam]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h3, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h2336, hlam, p2344_1]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h2338, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [h2339, hlam, p2344_0]
                · have p2344_0 := h2344c.1
                  have p2344_1 := h2344c.2.1
                  have p2344_2 := h2344c.2.2.1
                  have p2344_3 := h2344c.2.2.2
                  linarith only [hlam, p2344_0]
              · linarith only [h0, h2086, h2336, h2340, h2342, h2343, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2086, h2336, h2342, h4, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h2086, h2336, h2340, h2341, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h2336, h2340, h4, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h2086, h2336, h2339, hlam]
    · linarith only [h2086, h2336, h2337, h2338, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2400 | h2400
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2401 | h2401
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2402 | h2402
        · linarith only [h0, h2337, h2400, h2402, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h2336, h2402, h4, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h2336, h2337, h2401, h9, hlam]
    · linarith only [h2336, h2400, h9, hlam]

end R2N4
