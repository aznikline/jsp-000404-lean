import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S0
import Jsp000404.R1LeavesN7_27S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h1731 | h1731
  · linarith only [h0, h1731, h4, h744, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1733 | h1733
    · linarith only [h0, h1733, h600, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1735 | h1735
      · linarith only [h0, h1735, h713, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1737 | h1737
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1738 | h1738
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1739 | h1739
            · linarith only [h1739, h2, h745, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1741 | h1741
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1742 | h1742
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1743 | h1743
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1744 | h1744
                    · linarith only [h1737, h1744, h2, h745, hlam]
                    · rcases h0bigk with h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        rcases p1746_3 (m.d 0 1) (by simp) with h1748 | h1748
                        · rcases p1746_3 (m.d 0 2) (by simp) with h1749 | h1749
                          · linarith only [h0, h1749, hlam]
                          · rcases p1746_3 (m.d 0 3) (by simp) with h1751 | h1751
                            · linarith only [h1, h1751, hlam]
                            · linarith only [h1751, h4, hlam]
                        · linarith only [h0, h1748, hlam]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h743, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1746_1, u3ehi3]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        rcases p1746_3 (m.d 0 1) (by simp) with h1756 | h1756
                        · rcases p1746_3 (m.d 0 2) (by simp) with h1757 | h1757
                          · linarith only [h0, h1757, hlam]
                          · rcases p1746_3 (m.d 0 3) (by simp) with h1759 | h1759
                            · linarith only [h1, h1759, hlam]
                            · linarith only [h1759, h743, hlam]
                        · linarith only [h1756, h2, hlam]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        rcases p1746_3 (m.d 0 1) (by simp) with h1763 | h1763
                        · rcases p1746_3 (m.d 0 2) (by simp) with h1764 | h1764
                          · linarith only [h0, h1764, hlam]
                          · rcases p1746_3 (m.d 0 3) (by simp) with h1766 | h1766
                            · linarith only [h1, h1766, hlam]
                            · linarith only [h1766, h744, hlam]
                        · linarith only [h1763, h3, hlam]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h0, hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h4, hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h600, hlam, p1746_1]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h713, hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h1, hlam, p1746_1]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        rcases p1746_3 (m.d 0 1) (by simp) with h1776 | h1776
                        · rcases p1746_3 (m.d 0 2) (by simp) with h1777 | h1777
                          · linarith only [h1777, h4, hlam]
                          · rcases p1746_3 (m.d 0 3) (by simp) with h1779 | h1779
                            · rcases p1746_3 (m.d 0 4) (by simp) with h1780 | h1780
                              · linarith only [h1780, h743, hlam]
                              · linarith only [h1780, h600, hlam]
                            · linarith only [h1779, h4, hlam]
                        · linarith only [h0, h1776, hlam]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        rcases p1746_3 (m.d 0 1) (by simp) with h1786 | h1786
                        · rcases p1746_3 (m.d 0 2) (by simp) with h1787 | h1787
                          · linarith only [h1787, h4, hlam]
                          · rcases p1746_3 (m.d 0 3) (by simp) with h1789 | h1789
                            · rcases p1746_3 (m.d 0 4) (by simp) with h1790 | h1790
                              · linarith only [h1790, h743, hlam]
                              · rcases p1746_3 (m.d 0 5) (by simp) with h1792 | h1792
                                · linarith only [h1792, h744, hlam]
                                · linarith only [h1792, h745, hlam]
                            · linarith only [h1789, h743, hlam]
                        · linarith only [h1786, h2, hlam]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        rcases p1746_3 (m.d 0 1) (by simp) with h1797 | h1797
                        · rcases p1746_3 (m.d 0 2) (by simp) with h1798 | h1798
                          · linarith only [h1798, h4, hlam]
                          · rcases p1746_3 (m.d 0 3) (by simp) with h1800 | h1800
                            · rcases p1746_3 (m.d 0 4) (by simp) with h1801 | h1801
                              · linarith only [h1801, h743, hlam]
                              · rcases p1746_3 (m.d 0 5) (by simp) with h1803 | h1803
                                · linarith only [h1803, h744, hlam]
                                · rcases h0emin with h1805 | h1805 | h1805 | h1805 | h1805
                                  · rcases h2bigk with h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h4, h600, h745, hc12, hc23, hlam, hphi, p1746_1, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h4, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h600, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h713, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h0, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1731, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1733, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1735, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 2) (by simp) with h1817 | h1817
                                      · linarith only [h1817, hlam, p1806_0]
                                      · rcases p1806_3 (m.d 1 2) (by simp) with h1819 | h1819
                                        · linarith only [h1731, h1819, hlam]
                                        · rcases p1806_3 (m.d 2 3) (by simp) with h1821 | h1821
                                          · rcases p1806_3 (m.d 2 4) (by simp) with h1822 | h1822
                                            · linarith only [h1741, h1822, hlam]
                                            · linarith only [h1822, h600, hlam]
                                          · linarith only [h1821, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 2) (by simp) with h1826 | h1826
                                      · linarith only [h1826, h4, hlam]
                                      · linarith only [h0, h1826, hlam]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1743, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1806_1, u5ehi4]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h713, hc02, hc23, hlam, hphi, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 2) (by simp) with h1832 | h1832
                                      · linarith only [h1832, hlam, p1806_0]
                                      · rcases p1806_3 (m.d 1 2) (by simp) with h1834 | h1834
                                        · linarith only [h1733, h1834, hlam]
                                        · rcases p1806_3 (m.d 2 3) (by simp) with h1836 | h1836
                                          · rcases p1806_3 (m.d 2 4) (by simp) with h1837 | h1837
                                            · rcases p1806_3 (m.d 2 5) (by simp) with h1838 | h1838
                                              · linarith only [h1743, h1838, hlam]
                                              · linarith only [h1838, h713, hlam]
                                            · linarith only [h1837, hlam, p1806_0]
                                          · linarith only [h1836, h4, hlam]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 2) (by simp) with h1843 | h1843
                                      · linarith only [h1843, h600, hlam]
                                      · linarith only [h0, h1843, hlam]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1741, hlam, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h0, h1743, h600, h745, hc12, hc24, hlam, hphi, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 2) (by simp) with h1849 | h1849
                                      · linarith only [h1849, hlam, p1806_0]
                                      · rcases p1806_3 (m.d 1 2) (by simp) with h1851 | h1851
                                        · linarith only [h1735, h1851, hlam]
                                        · rcases p1806_3 (m.d 2 3) (by simp) with h1853 | h1853
                                          · rcases p1806_3 (m.d 2 4) (by simp) with h1854 | h1854
                                            · rcases p1806_3 (m.d 2 5) (by simp) with h1855 | h1855
                                              · rcases h5bigk with h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1746_1, p1856_1, u5ehi1]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h713, hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1744, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1746_1, p1856_1, u3ehi3]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h745, hlam, p1856_1]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h3, hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1735, hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1744, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1856_1, u3ehi3]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1739, hlam, p1856_1]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  rcases p1856_3 (m.d 0 5) (by simp) with h1867 | h1867
                                                  · linarith only [h1867, h713, hlam]
                                                  · rcases p1856_3 (m.d 1 5) (by simp) with h1869 | h1869
                                                    · linarith only [h1735, h1869, hlam]
                                                    · rcases p1856_3 (m.d 2 5) (by simp) with h1871 | h1871
                                                      · rcases p1856_3 (m.d 3 5) (by simp) with h1872 | h1872
                                                        · linarith only [h1742, h1872, hlam]
                                                        · rcases p1856_3 (m.d 4 5) (by simp) with h1874 | h1874
                                                          · linarith only [h1743, h1874, hlam]
                                                          · linarith only [h1874, h745, hlam]
                                                      · linarith only [h1871, h713, hlam]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  rcases p1856_3 (m.d 0 5) (by simp) with h1878 | h1878
                                                  · linarith only [h1878, h713, hlam]
                                                  · linarith only [h1878, h3, hlam]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  rcases p1856_3 (m.d 0 5) (by simp) with h1882 | h1882
                                                  · linarith only [h1882, h713, hlam]
                                                  · linarith only [h1882, h744, hlam]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1737, h1741, h1743, h2, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1856_1, u3ehi3]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h744, hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1738, hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1742, hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1744, hlam, p1856_1]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1744, h744, hc45, hlam, hphi, ht34, p1856_1, u3ehi3]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1738, h1744, hc45, hlam, hphi, ht34, p1856_1, u3ehi3]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1743, hlam, p1856_0]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [h1741, h1743, h1744, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1856_1, u3ehi3]
                                                · have p1856_0 := h1856c.1
                                                  have p1856_1 := h1856c.2.1
                                                  have p1856_2 := h1856c.2.2.1
                                                  have p1856_3 := h1856c.2.2.2
                                                  linarith only [hlam, p1856_0]
                                              · linarith only [h1855, hlam, p1806_0]
                                            · linarith only [h1854, h600, hlam]
                                          · linarith only [h1853, h4, hlam]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 2) (by simp) with h1899 | h1899
                                      · linarith only [h1899, h713, hlam]
                                      · linarith only [h0, h1899, hlam]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1742, hlam, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1743, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                  · linarith only [h1805, h4, hc23, hlam, ht01, ht12]
                                  · rcases h2bigk with h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p1906_1]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h4, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h600, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h713, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h0, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h1731, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h1733, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h1735, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      rcases p1906_3 (m.d 0 2) (by simp) with h1917 | h1917
                                      · linarith only [h1917, hlam, p1906_0]
                                      · rcases p1906_3 (m.d 1 2) (by simp) with h1919 | h1919
                                        · linarith only [h1731, h1919, hlam]
                                        · rcases p1906_3 (m.d 2 3) (by simp) with h1921 | h1921
                                          · rcases p1906_3 (m.d 2 4) (by simp) with h1922 | h1922
                                            · linarith only [h1741, h1922, hlam]
                                            · linarith only [h1922, h600, hlam]
                                          · linarith only [h1921, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      rcases p1906_3 (m.d 0 2) (by simp) with h1926 | h1926
                                      · linarith only [h1926, h4, hlam]
                                      · linarith only [h0, h1926, hlam]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h1743, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1906_1, u5ehi4]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h713, hc02, hc23, hlam, hphi, p1906_1]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      rcases p1906_3 (m.d 0 2) (by simp) with h1932 | h1932
                                      · linarith only [h1932, hlam, p1906_0]
                                      · rcases p1906_3 (m.d 1 2) (by simp) with h1934 | h1934
                                        · linarith only [h1733, h1934, hlam]
                                        · rcases p1906_3 (m.d 2 3) (by simp) with h1936 | h1936
                                          · rcases p1906_3 (m.d 2 4) (by simp) with h1937 | h1937
                                            · rcases p1906_3 (m.d 2 5) (by simp) with h1938 | h1938
                                              · linarith only [h1743, h1938, hlam]
                                              · linarith only [h1938, h713, hlam]
                                            · linarith only [h1937, hlam, p1906_0]
                                          · linarith only [h1936, h4, hlam]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      rcases p1906_3 (m.d 0 2) (by simp) with h1943 | h1943
                                      · linarith only [h1943, h600, hlam]
                                      · linarith only [h0, h1943, hlam]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h1741, hlam, p1906_1]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h1737, h1743, h2, h745, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1906_1, u3ehi3]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      rcases p1906_3 (m.d 0 2) (by simp) with h1949 | h1949
                                      · linarith only [h1949, hlam, p1906_0]
                                      · rcases p1906_3 (m.d 1 2) (by simp) with h1951 | h1951
                                        · linarith only [h1735, h1951, hlam]
                                        · rcases p1906_3 (m.d 2 3) (by simp) with h1953 | h1953
                                          · rcases p1906_3 (m.d 2 4) (by simp) with h1954 | h1954
                                            · rcases p1906_3 (m.d 2 5) (by simp) with h1955 | h1955
                                              · rcases h5bigk with h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1738, h1744, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1746_1, p1956_1, u3ehi3]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h713, hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1744, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1746_1, p1956_1, u3ehi3]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h745, hlam, p1956_1]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h3, hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1735, hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1744, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1956_1, u3ehi3]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1739, hlam, p1956_1]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  rcases p1956_3 (m.d 0 5) (by simp) with h1967 | h1967
                                                  · linarith only [h1967, h713, hlam]
                                                  · rcases p1956_3 (m.d 1 5) (by simp) with h1969 | h1969
                                                    · linarith only [h1735, h1969, hlam]
                                                    · rcases p1956_3 (m.d 2 5) (by simp) with h1971 | h1971
                                                      · rcases p1956_3 (m.d 3 5) (by simp) with h1972 | h1972
                                                        · linarith only [h1742, h1972, hlam]
                                                        · rcases p1956_3 (m.d 4 5) (by simp) with h1974 | h1974
                                                          · linarith only [h1743, h1974, hlam]
                                                          · linarith only [h1974, h745, hlam]
                                                      · linarith only [h1971, h713, hlam]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  rcases p1956_3 (m.d 0 5) (by simp) with h1978 | h1978
                                                  · linarith only [h1978, h713, hlam]
                                                  · linarith only [h1978, h3, hlam]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  rcases p1956_3 (m.d 0 5) (by simp) with h1982 | h1982
                                                  · linarith only [h1982, h713, hlam]
                                                  · linarith only [h1982, h744, hlam]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1737, h1741, h1743, h2, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1956_1, u3ehi3]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h744, hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1738, hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1742, hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1744, hlam, p1956_1]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1744, h744, hc45, hlam, hphi, ht34, p1956_1, u3ehi3]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1738, h1744, hc45, hlam, hphi, ht34, p1956_1, u3ehi3]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1743, hlam, p1956_0]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [h1741, h1743, h1744, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1956_1, u3ehi3]
                                                · have p1956_0 := h1956c.1
                                                  have p1956_1 := h1956c.2.1
                                                  have p1956_2 := h1956c.2.2.1
                                                  have p1956_3 := h1956c.2.2.2
                                                  linarith only [hlam, p1956_0]
                                              · linarith only [h1955, hlam, p1906_0]
                                            · linarith only [h1954, h600, hlam]
                                          · linarith only [h1953, h4, hlam]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      rcases p1906_3 (m.d 0 2) (by simp) with h1999 | h1999
                                      · linarith only [h1999, h713, hlam]
                                      · linarith only [h0, h1999, hlam]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h1742, hlam, p1906_1]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [h1743, hlam, p1906_0]
                                    · have p1906_0 := h1906c.1
                                      have p1906_1 := h1906c.2.1
                                      have p1906_2 := h1906c.2.2.1
                                      have p1906_3 := h1906c.2.2.2
                                      linarith only [hlam, p1906_0]
                                  · linarith only [h1805, h4, h745, hc23, hlam, ht01, ht12, p1746_1]
                                  · linarith only [h1805, h4, hc23, hlam, ht01, ht12, p1746_1]
                            · linarith only [h1800, h744, hlam]
                        · linarith only [h1797, h3, hlam]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h2, hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h0, h1741, h1743, h745, hc12, hc23, hlam, hphi, p1746_1]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h743, hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h745, hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h3, hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h0, h1741, h1743, h745, hc12, hc23, hlam, hphi, p1746_1]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h744, hlam, p1746_0]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [h1737, h1741, h1743, h2, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1746_1, u3ehi3]
                      · have p1746_0 := h1746c.1
                        have p1746_1 := h1746c.2.1
                        have p1746_2 := h1746c.2.2.1
                        have p1746_3 := h1746c.2.2.2
                        linarith only [hlam, p1746_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2019 | h2019
                    · linarith only [h0, h1743, h2019, h600, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c | h2021c
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        rcases p2021_3 (m.d 0 1) (by simp) with h2023 | h2023
                        · rcases p2021_3 (m.d 0 2) (by simp) with h2024 | h2024
                          · linarith only [h0, h2024, hlam]
                          · rcases p2021_3 (m.d 0 3) (by simp) with h2026 | h2026
                            · linarith only [h1, h2026, hlam]
                            · linarith only [h2026, h4, hlam]
                        · linarith only [h0, h2023, hlam]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h1, h1738, hc01, hlam, hphi, ht0b, ht5b, p2021_1, u5ehi3]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        rcases p2021_3 (m.d 0 1) (by simp) with h2031 | h2031
                        · rcases p2021_3 (m.d 0 2) (by simp) with h2032 | h2032
                          · linarith only [h0, h2032, hlam]
                          · rcases p2021_3 (m.d 0 3) (by simp) with h2034 | h2034
                            · linarith only [h1, h2034, hlam]
                            · linarith only [h2034, h743, hlam]
                        · linarith only [h2, h2031, hlam]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        rcases p2021_3 (m.d 0 1) (by simp) with h2038 | h2038
                        · rcases p2021_3 (m.d 0 2) (by simp) with h2039 | h2039
                          · linarith only [h0, h2039, hlam]
                          · rcases p2021_3 (m.d 0 3) (by simp) with h2041 | h2041
                            · linarith only [h1, h2041, hlam]
                            · linarith only [h2041, h744, hlam]
                        · linarith only [h2038, h3, hlam]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h0, hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h4, hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h600, hlam, p2021_1]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h713, hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h1, hlam, p2021_1]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        rcases p2021_3 (m.d 0 1) (by simp) with h2051 | h2051
                        · rcases p2021_3 (m.d 0 2) (by simp) with h2052 | h2052
                          · linarith only [h2052, h4, hlam]
                          · rcases p2021_3 (m.d 0 3) (by simp) with h2054 | h2054
                            · rcases p2021_3 (m.d 0 4) (by simp) with h2055 | h2055
                              · linarith only [h2055, h743, hlam]
                              · linarith only [h2055, h600, hlam]
                            · linarith only [h2054, h4, hlam]
                        · linarith only [h0, h2051, hlam]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        rcases p2021_3 (m.d 0 1) (by simp) with h2061 | h2061
                        · rcases p2021_3 (m.d 0 2) (by simp) with h2062 | h2062
                          · linarith only [h2062, h4, hlam]
                          · rcases p2021_3 (m.d 0 3) (by simp) with h2064 | h2064
                            · rcases p2021_3 (m.d 0 4) (by simp) with h2065 | h2065
                              · linarith only [h2065, h743, hlam]
                              · rcases p2021_3 (m.d 0 5) (by simp) with h2067 | h2067
                                · linarith only [h2067, h744, hlam]
                                · linarith only [h2067, h745, hlam]
                            · linarith only [h2064, h743, hlam]
                        · linarith only [h2, h2061, hlam]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        rcases p2021_3 (m.d 0 1) (by simp) with h2072 | h2072
                        · rcases p2021_3 (m.d 0 2) (by simp) with h2073 | h2073
                          · linarith only [h2073, h4, hlam]
                          · rcases p2021_3 (m.d 0 3) (by simp) with h2075 | h2075
                            · rcases p2021_3 (m.d 0 4) (by simp) with h2076 | h2076
                              · linarith only [h2076, h743, hlam]
                              · rcases p2021_3 (m.d 0 5) (by simp) with h2078 | h2078
                                · linarith only [h2078, h744, hlam]
                                · rcases h0emin with h2080 | h2080 | h2080 | h2080 | h2080
                                  · rcases h2bigk with h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c | h2081c
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h600, hc12, hc24, hlam, hphi, p2081_1]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h4, hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h600, hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h713, hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h0, hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h1731, hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h1733, hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h1735, hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      rcases p2081_3 (m.d 0 2) (by simp) with h2092 | h2092
                                      · linarith only [h2092, hlam, p2081_0]
                                      · rcases p2081_3 (m.d 1 2) (by simp) with h2094 | h2094
                                        · linarith only [h1731, h2094, hlam]
                                        · rcases p2081_3 (m.d 2 3) (by simp) with h2096 | h2096
                                          · rcases p2081_3 (m.d 2 4) (by simp) with h2097 | h2097
                                            · linarith only [h1741, h2097, hlam]
                                            · linarith only [h2097, h600, hlam]
                                          · linarith only [h2096, hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      rcases p2081_3 (m.d 0 2) (by simp) with h2101 | h2101
                                      · linarith only [h2101, h4, hlam]
                                      · linarith only [h0, h2101, hlam]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h600, hc02, hc23, hlam, hphi, p2081_1]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h0, h713, hc12, hc23, hlam, hphi, p2081_1]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h0, h1737, h1739, h1743, h3, h4, hc12, hc23, hc45, hlam, hphi, ht34, p2021_1, p2081_1, u3ehi3]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h1737, h1739, h1743, h3, h4, hc12, hc23, hc45, hlam, hphi, ht34, p2021_1, p2081_1, u3ehi3]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h1741, hlam, p2081_1]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [hlam, p2081_0]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h1743, hlam, p2081_1]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      rcases p2081_3 (m.d 0 2) (by simp) with h2112 | h2112
                                      · linarith only [h2112, hlam, p2081_0]
                                      · rcases p2081_3 (m.d 1 2) (by simp) with h2114 | h2114
                                        · linarith only [h1735, h2114, hlam]
                                        · rcases p2081_3 (m.d 2 3) (by simp) with h2116 | h2116
                                          · rcases p2081_3 (m.d 2 4) (by simp) with h2117 | h2117
                                            · linarith only [h1743, h2117, hlam]
                                            · linarith only [h2117, h600, hlam]
                                          · linarith only [h2116, h4, hlam]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      rcases p2081_3 (m.d 0 2) (by simp) with h2121 | h2121
                                      · linarith only [h2121, h713, hlam]
                                      · linarith only [h0, h2121, hlam]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h1742, hlam, p2081_1]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [h0, h600, hc12, hc25, hlam, hphi, p2081_1]
                                    · have p2081_0 := h2081c.1
                                      have p2081_1 := h2081c.2.1
                                      have p2081_2 := h2081c.2.2.1
                                      have p2081_3 := h2081c.2.2.2
                                      linarith only [hlam, p2081_0]
                                  · linarith only [h2080, h600, hc24, hlam, ht01, ht12]
                                  · rcases h2bigk with h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h1737, h1739, h1743, h3, h4, h600, hc12, hc23, hc45, hlam, hphi, ht34, p2021_1, p2128_1, u3ehi3]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h4, hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h600, hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h713, hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h0, hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h1731, hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h1733, hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h1735, hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      rcases p2128_3 (m.d 0 2) (by simp) with h2139 | h2139
                                      · linarith only [h2139, hlam, p2128_0]
                                      · rcases p2128_3 (m.d 1 2) (by simp) with h2141 | h2141
                                        · linarith only [h1731, h2141, hlam]
                                        · rcases p2128_3 (m.d 2 3) (by simp) with h2143 | h2143
                                          · rcases p2128_3 (m.d 2 4) (by simp) with h2144 | h2144
                                            · linarith only [h1741, h2144, hlam]
                                            · linarith only [h2144, h600, hlam]
                                          · linarith only [h2143, hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      rcases p2128_3 (m.d 0 2) (by simp) with h2148 | h2148
                                      · linarith only [h2148, h4, hlam]
                                      · linarith only [h0, h2148, hlam]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h600, hc02, hc23, hlam, hphi, p2128_1]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h0, h713, hc12, hc23, hlam, hphi, p2128_1]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h0, h1737, h1739, h1743, h3, h4, hc12, hc23, hc45, hlam, hphi, ht34, p2021_1, p2128_1, u3ehi3]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h1737, h1739, h1743, h3, h4, hc12, hc23, hc45, hlam, hphi, ht34, p2021_1, p2128_1, u3ehi3]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h1741, hlam, p2128_1]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [hlam, p2128_0]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h1743, hlam, p2128_1]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      rcases p2128_3 (m.d 0 2) (by simp) with h2159 | h2159
                                      · linarith only [h2159, hlam, p2128_0]
                                      · rcases p2128_3 (m.d 1 2) (by simp) with h2161 | h2161
                                        · linarith only [h1735, h2161, hlam]
                                        · rcases p2128_3 (m.d 2 3) (by simp) with h2163 | h2163
                                          · rcases p2128_3 (m.d 2 4) (by simp) with h2164 | h2164
                                            · linarith only [h1743, h2164, hlam]
                                            · linarith only [h2164, h600, hlam]
                                          · linarith only [h2163, h4, hlam]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      rcases p2128_3 (m.d 0 2) (by simp) with h2168 | h2168
                                      · linarith only [h2168, h713, hlam]
                                      · linarith only [h0, h2168, hlam]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h1742, hlam, p2128_1]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [h0, h600, hc12, hc25, hlam, hphi, p2128_1]
                                    · have p2128_0 := h2128c.1
                                      have p2128_1 := h2128c.2.1
                                      have p2128_2 := h2128c.2.2.1
                                      have p2128_3 := h2128c.2.2.2
                                      linarith only [hlam, p2128_0]
                                  · linarith only [h2080, h4, h745, hc23, hlam, ht01, ht12, p2021_1]
                                  · linarith only [h2080, h4, hc23, hlam, ht01, ht12, p2021_1]
                            · linarith only [h2075, h744, hlam]
                        · linarith only [h2072, h3, hlam]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h2, hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h0, h745, hc12, hc45, hlam, hphi, ht23, ht34, p2021_1]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h743, hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h745, hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h3, hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        rcases p2021_3 (m.d 0 1) (by simp) with h2184 | h2184
                        · rcases p2021_3 (m.d 0 2) (by simp) with h2185 | h2185
                          · linarith only [h2185, h713, hlam]
                          · rcases p2021_3 (m.d 0 3) (by simp) with h2187 | h2187
                            · rcases p2021_3 (m.d 0 4) (by simp) with h2188 | h2188
                              · linarith only [h2188, h745, hlam]
                              · linarith only [h2188, h600, hlam]
                            · linarith only [h2187, h4, hlam]
                        · linarith only [h0, h2184, hlam]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h744, hlam, p2021_0]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [h1743, h713, h743, hc45, hlam, hphi, ht34, p2021_1, u3ehi3]
                      · have p2021_0 := h2021c.1
                        have p2021_1 := h2021c.2.1
                        have p2021_2 := h2021c.2.2.1
                        have p2021_3 := h2021c.2.2.2
                        linarith only [hlam, p2021_0]
                · linarith only [h1, h1738, h1742, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h1, h1738, h1741, h4, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1737, h1738, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1737, h743, h745, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h745 | h745
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  linarith only [h743, h744, hc35, hlam, hphi, u3ehi3]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h744 | h744
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h2201 | h2201
  · linarith only [h2201, h743, hc34, hlam, hphi, u3ehi4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2203 | h2203
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2204 | h2204
      · linarith only [h0, h2204, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2206 | h2206
        · linarith only [h0, h2203, h2206, h4, h600, h743, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2208 | h2208
          · linarith only [h0, h2208, h713, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2210 | h2210
            · linarith only [h1, h2210, h743, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2212 | h2212
              · linarith only [h1, h2201, h2212, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2214 | h2214
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2215 | h2215
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2216 | h2216
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2217 | h2217
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2218 | h2218
                        · rcases h0bigk with h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            rcases p2219_3 (m.d 0 1) (by simp) with h2221 | h2221
                            · rcases p2219_3 (m.d 0 2) (by simp) with h2222 | h2222
                              · linarith only [h0, h2222, hlam]
                              · rcases p2219_3 (m.d 0 3) (by simp) with h2224 | h2224
                                · linarith only [h1, h2224, hlam]
                                · linarith only [h2224, h4, hlam]
                            · linarith only [h0, h2221, hlam]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            rcases p2219_3 (m.d 0 1) (by simp) with h2228 | h2228
                            · rcases p2219_3 (m.d 0 2) (by simp) with h2229 | h2229
                              · linarith only [h0, h2229, hlam]
                              · rcases p2219_3 (m.d 0 3) (by simp) with h2231 | h2231
                                · linarith only [h1, h2231, hlam]
                                · rcases p2219_3 (m.d 0 4) (by simp) with h2233 | h2233
                                  · linarith only [h2, h2233, hlam]
                                  · linarith only [h2233, h743, hlam]
                            · linarith only [h1, h2228, hlam]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h2, h2214, hc01, hlam, hphi, ht0b, ht5b, p2219_1, u5ehi4]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            rcases p2219_3 (m.d 0 1) (by simp) with h2238 | h2238
                            · rcases p2219_3 (m.d 0 2) (by simp) with h2239 | h2239
                              · linarith only [h0, h2239, hlam]
                              · rcases p2219_3 (m.d 0 3) (by simp) with h2241 | h2241
                                · linarith only [h1, h2241, hlam]
                                · rcases p2219_3 (m.d 0 4) (by simp) with h2243 | h2243
                                  · linarith only [h2, h2243, hlam]
                                  · linarith only [h2203, h2243, hlam]
                            · linarith only [h2238, h3, hlam]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h0, hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h4, hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h600, hlam, p2219_1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h713, hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h1, hlam, p2219_1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h0, h2201, h2215, h2218, hc12, hc23, hlam, hphi, p2219_1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h743, hlam, p2219_1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h2201, hlam, p2219_1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h2, hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h0, h2215, h743, hc12, hc23, hlam, hphi, p2219_1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h2215, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2219_1, u3ehi0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h1, h2201, h2215, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2219_1, u3ehi1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h3, hlam, p2219_0]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h0, h2201, h2215, h2218, hc12, hc23, hlam, hphi, p2219_1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h1, h2201, h2215, h2218, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2219_1, u3ehi1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [h2203, hlam, p2219_1]
                          · have p2219_0 := h2219c.1
                            have p2219_1 := h2219c.2.1
                            have p2219_2 := h2219c.2.2.1
                            have p2219_3 := h2219c.2.2.2
                            linarith only [hlam, p2219_0]
                        · linarith only [h2, h2214, h2218, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h2, h2214, h2215, h2217, h743, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h2215, h2216, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2270 | h2270
                    · linarith only [h2215, h2270, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2272 | h2272
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2273 | h2273
                        · rcases h0bigk with h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            rcases p2274_3 (m.d 0 1) (by simp) with h2276 | h2276
                            · rcases p2274_3 (m.d 0 2) (by simp) with h2277 | h2277
                              · linarith only [h0, h2277, hlam]
                              · rcases p2274_3 (m.d 0 3) (by simp) with h2279 | h2279
                                · linarith only [h1, h2279, hlam]
                                · linarith only [h2279, h4, hlam]
                            · linarith only [h0, h2276, hlam]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            rcases p2274_3 (m.d 0 1) (by simp) with h2283 | h2283
                            · rcases p2274_3 (m.d 0 2) (by simp) with h2284 | h2284
                              · linarith only [h0, h2284, hlam]
                              · rcases p2274_3 (m.d 0 3) (by simp) with h2286 | h2286
                                · linarith only [h1, h2286, hlam]
                                · rcases p2274_3 (m.d 0 4) (by simp) with h2288 | h2288
                                  · linarith only [h2, h2288, hlam]
                                  · linarith only [h2288, h743, hlam]
                            · linarith only [h1, h2283, hlam]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h2, h2214, hc01, hlam, hphi, ht0b, ht5b, p2274_1, u5ehi4]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            rcases p2274_3 (m.d 0 1) (by simp) with h2293 | h2293
                            · rcases p2274_3 (m.d 0 2) (by simp) with h2294 | h2294
                              · linarith only [h0, h2294, hlam]
                              · rcases p2274_3 (m.d 0 3) (by simp) with h2296 | h2296
                                · linarith only [h1, h2296, hlam]
                                · rcases p2274_3 (m.d 0 4) (by simp) with h2298 | h2298
                                  · linarith only [h2, h2298, hlam]
                                  · linarith only [h2203, h2298, hlam]
                            · linarith only [h2293, h3, hlam]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h0, hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h4, hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h600, hlam, p2274_1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h713, hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h1, hlam, p2274_1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h0, h2270, h2273, h4, hc12, hc34, hlam, hphi, ht23, p2274_1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h743, hlam, p2274_1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h2201, hlam, p2274_1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h2, hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            rcases p2274_3 (m.d 0 1) (by simp) with h2313 | h2313
                            · rcases p2274_3 (m.d 0 2) (by simp) with h2314 | h2314
                              · linarith only [h2314, h600, hlam]
                              · rcases p2274_3 (m.d 0 3) (by simp) with h2316 | h2316
                                · linarith only [h2316, h743, hlam]
                                · linarith only [h2316, h4, hlam]
                            · linarith only [h0, h2313, hlam]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h1, h743, hc34, hlam, hphi, p2274_1, u3ehi1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h1, h2201, h743, hc34, hlam, hphi, p2274_1, u3ehi1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h3, hlam, p2274_0]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            rcases p2274_3 (m.d 0 1) (by simp) with h2324 | h2324
                            · rcases p2274_3 (m.d 0 2) (by simp) with h2325 | h2325
                              · linarith only [h2325, h713, hlam]
                              · rcases p2274_3 (m.d 0 3) (by simp) with h2327 | h2327
                                · linarith only [h2201, h2327, hlam]
                                · linarith only [h2327, h4, hlam]
                            · linarith only [h0, h2324, hlam]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h1, h2201, h2273, hc34, hlam, hphi, p2274_1, u3ehi1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [h2203, hlam, p2274_1]
                          · have p2274_0 := h2274c.1
                            have p2274_1 := h2274c.2.1
                            have p2274_2 := h2274c.2.2.1
                            have p2274_3 := h2274c.2.2.2
                            linarith only [hlam, p2274_0]
                        · linarith only [h2, h2203, h2214, h2215, h2273, h600, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · linarith only [h2, h2214, h2272, h600, hlam]
                · linarith only [h2203, h2210, h2214, h743, hc34, hlam, hphi, u3ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2337 | h2337
      · linarith only [h0, h2337, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2339 | h2339
        · linarith only [h0, h2339, h600, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2341 | h2341
          · linarith only [h0, h2341, h713, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2343 | h2343
            · linarith only [h1, h2203, h2343, h743, hc45, hlam, hphi, ht34, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2345 | h2345
              · linarith only [h1, h2203, h2345, h743, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2347 | h2347
                · linarith only [h2, h2203, h2347, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2349 | h2349
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2350 | h2350
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2351 | h2351
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2352 | h2352
                        · linarith only [h2203, h2352, h743, hc34, hlam, hphi, u3ehi0]
                        · linarith only [h1, h2349, h2351, h2352, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h2349, h2351, h743, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h1, h2349, h2350, h743, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2357 | h2357
                    · linarith only [h2349, h2357, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2359 | h2359
                      · linarith only [h1, h2203, h2349, h2359, h743, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2361 | h2361
                        · linarith only [h2349, h2359, h2361, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1, h2361, h743, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h743 | h743
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h713 | h713
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h600 | h600
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h2364 | h2364
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2365 | h2365
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2366 | h2366
      · linarith only [h0, h2366, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2368 | h2368
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2369 | h2369
          · linarith only [h0, h2364, h2369, h3, hlam]
          · linarith only [h2368, h2369, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2372 | h2372
          · linarith only [h2368, h2372, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2374 | h2374
            · linarith only [h2, h2374, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2376 | h2376
              · linarith only [h0, h2376, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h2364, h2366, h2376, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2379 | h2379
      · linarith only [h0, h2379, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2381 | h2381
        · linarith only [h2364, h2365, h2381, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2383 | h2383
          · linarith only [h2381, h2383, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2385 | h2385
            · linarith only [h2, h2385, h3, hlam]
            · linarith only [h2364, h2365, h2385, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2388 | h2388
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2389 | h2389
      · linarith only [h0, h2389, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2391 | h2391
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2392 | h2392
          · linarith only [h1, h2392, h3, hlam]
          · linarith only [h2391, h2392, hc35, hlam, hphi, u3ehi3]
        · linarith only [h2364, h2388, h2391, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2396 | h2396
      · linarith only [h0, h2396, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2398 | h2398
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2399 | h2399
          · linarith only [h1, h2399, h3, hlam]
          · linarith only [h2398, h2399, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2402 | h2402
          · linarith only [h2398, h2402, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2404 | h2404
            · linarith only [h2, h2404, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2406 | h2406
              · linarith only [h0, h2406, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2408 | h2408
                · linarith only [h0, h2388, h2408, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2410 | h2410
                  · linarith only [h1, h2396, h2406, h2410, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2412 | h2412
                    · linarith only [h1, h2410, h2412, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2414 | h2414
                      · linarith only [h2, h2402, h2410, h2412, h2414, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h2, h2412, h2414, h3, hc35, hlam, hphi, u3ehi1]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3

end R2N4
