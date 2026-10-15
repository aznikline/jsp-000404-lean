import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h1745 | h1745
  · linarith only [h1745, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1747 | h1747
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1748 | h1748
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1749 | h1749
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1750 | h1750
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1751 | h1751
            · linarith only [h1, h1751, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1753 | h1753
              · linarith only [h1745, h1753, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1755 | h1755
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1756 | h1756
                  · linarith only [h1756, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1758 | h1758
                    · linarith only [h1745, h1748, h1758, h2, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1760 | h1760
                      · linarith only [h1745, h1749, h1755, h1756, h1760, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h0, h1749, hc01, hlam, hphi, ht0b, ht5b, p1762_1, u5ehi2]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          rcases p1762_3 (m.d 0 1) (by simp) with h1765 | h1765
                          · rcases p1762_3 (m.d 0 2) (by simp) with h1766 | h1766
                            · linarith only [h0, h1766, hlam]
                            · linarith only [h1766, h4, hlam]
                          · linarith only [h1, h1765, hlam]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          rcases p1762_3 (m.d 0 1) (by simp) with h1770 | h1770
                          · rcases p1762_3 (m.d 0 2) (by simp) with h1771 | h1771
                            · linarith only [h0, h1771, hlam]
                            · linarith only [h1771, h5, hlam]
                          · linarith only [h1770, h2, hlam]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          rcases p1762_3 (m.d 0 1) (by simp) with h1775 | h1775
                          · rcases p1762_3 (m.d 0 2) (by simp) with h1776 | h1776
                            · linarith only [h0, h1776, hlam]
                            · linarith only [h1776, h6, hlam]
                          · linarith only [h1775, h3, hlam]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h0, hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          rcases p1762_3 (m.d 0 1) (by simp) with h1782 | h1782
                          · rcases p1762_3 (m.d 0 2) (by simp) with h1783 | h1783
                            · rcases p1762_3 (m.d 0 3) (by simp) with h1784 | h1784
                              · linarith only [h1784, h4, hlam]
                              · rcases p1762_3 (m.d 0 4) (by simp) with h1786 | h1786
                                · linarith only [h1786, h5, hlam]
                                · rcases p1762_3 (m.d 0 5) (by simp) with h1788 | h1788
                                  · linarith only [h1788, h6, hlam]
                                  · linarith only [h1788, h8, hlam]
                            · linarith only [h1783, h4, hlam]
                          · linarith only [h1, h1782, hlam]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          rcases p1762_3 (m.d 0 1) (by simp) with h1793 | h1793
                          · rcases p1762_3 (m.d 0 2) (by simp) with h1794 | h1794
                            · rcases p1762_3 (m.d 0 3) (by simp) with h1795 | h1795
                              · linarith only [h1795, h4, hlam]
                              · linarith only [h1795, h7, hlam]
                            · linarith only [h1794, h5, hlam]
                          · linarith only [h1793, h2, hlam]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          rcases p1762_3 (m.d 0 1) (by simp) with h1800 | h1800
                          · rcases p1762_3 (m.d 0 2) (by simp) with h1801 | h1801
                            · rcases p1762_3 (m.d 0 3) (by simp) with h1802 | h1802
                              · linarith only [h1802, h4, hlam]
                              · rcases p1762_3 (m.d 0 4) (by simp) with h1804 | h1804
                                · linarith only [h1804, h5, hlam]
                                · rcases p1762_3 (m.d 0 5) (by simp) with h1806 | h1806
                                  · linarith only [h1806, h6, hlam]
                                  · rcases h2bigk with h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h0, h1749, h1755, h1756, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      rcases p1808_3 (m.d 0 2) (by simp) with h1811 | h1811
                                      · rcases p1808_3 (m.d 1 2) (by simp) with h1812 | h1812
                                        · linarith only [h0, h1812, hlam]
                                        · linarith only [h1747, h1812, hlam]
                                      · linarith only [h1811, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      rcases p1808_3 (m.d 0 2) (by simp) with h1816 | h1816
                                      · rcases p1808_3 (m.d 1 2) (by simp) with h1817 | h1817
                                        · linarith only [h0, h1817, hlam]
                                        · linarith only [h1748, h1817, hlam]
                                      · linarith only [h1816, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      rcases p1808_3 (m.d 0 2) (by simp) with h1821 | h1821
                                      · rcases p1808_3 (m.d 1 2) (by simp) with h1822 | h1822
                                        · linarith only [h0, h1822, hlam]
                                        · linarith only [h1749, h1822, hlam]
                                      · linarith only [h1821, hlam, p1808_0]
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
                                      linarith only [h0, h1755, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      rcases p1808_3 (m.d 0 2) (by simp) with h1829 | h1829
                                      · rcases p1808_3 (m.d 1 2) (by simp) with h1830 | h1830
                                        · rcases p1808_3 (m.d 2 3) (by simp) with h1831 | h1831
                                          · linarith only [h1747, h1831, hlam]
                                          · linarith only [h1755, h1831, hlam]
                                        · linarith only [h1830, hlam, p1808_0]
                                      · linarith only [h1829, h5, hlam]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h0, h1755, h1756, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h4, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h1747, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h0, h1, h1747, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1762_1, p1808_1]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h1756, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h5, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h1748, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h1755, hlam, p1808_1]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h1758, hlam, p1808_1]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h6, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h1749, hlam, p1808_0]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h0, h1749, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1762_1, p1808_1]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [h0, h1749, h1755, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1762_1, p1808_1]
                                    · have p1808_0 := h1808c.1
                                      have p1808_1 := h1808c.2.1
                                      have p1808_2 := h1808c.2.2.1
                                      have p1808_3 := h1808c.2.2.2
                                      linarith only [hlam, p1808_0]
                            · linarith only [h1801, h6, hlam]
                          · linarith only [h1800, h3, hlam]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h1, hlam, p1762_1]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h4, hlam, p1762_1]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h1748, h1755, h1760, h2, h8, hc34, hc45, hlam, hphi, p1762_1]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h8, hlam, p1762_1]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h2, hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h5, hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h7, hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h1745, hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h3, hlam, p1762_0]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h6, hlam, p1762_1]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [h1755, h1760, h4, h8, hc34, hc45, hlam, hphi, p1762_1]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          rcases p1762_3 (m.d 0 1) (by simp) with h1867 | h1867
                          · rcases p1762_3 (m.d 0 2) (by simp) with h1868 | h1868
                            · rcases p1762_3 (m.d 0 3) (by simp) with h1869 | h1869
                              · linarith only [h1869, h8, hlam]
                              · linarith only [h1869, h7, hlam]
                            · linarith only [h1868, h5, hlam]
                          · linarith only [h1867, h2, hlam]
                        · have p1762_0 := h1762c.1
                          have p1762_1 := h1762c.2.1
                          have p1762_2 := h1762c.2.2.1
                          have p1762_3 := h1762c.2.2.2
                          linarith only [hlam, p1762_0]
                · linarith only [h1755, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1747, h1750, h7, h8, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1877 | h1877
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1878 | h1878
            · linarith only [h0, h1747, h1749, h1878, h6, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1880 | h1880
              · linarith only [h1745, h1880, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1882 | h1882
                · linarith only [h0, h1747, h1749, h1882, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1882, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1877, h7, h8, hc13, hc35, hlam, hphi]
      · linarith only [h1745, h1747, h1748, h5, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1887 | h1887
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1888 | h1888
        · linarith only [h1747, h1888, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1890 | h1890
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1891 | h1891
            · linarith only [h1747, h1887, h1891, h4, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1893 | h1893
              · linarith only [h1745, h1747, h1887, h1893, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1895 | h1895
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1896 | h1896
                  · linarith only [h1896, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1898 | h1898
                    · linarith only [h1745, h1747, h1887, h1898, h4, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1900 | h1900
                      · linarith only [h1745, h1747, h1887, h1895, h1900, h4, h8, hlam]
                      · linarith only [h1747, h1887, h1900, h4, h8, hc24, hc45, hlam, hphi]
                · linarith only [h1747, h1887, h1895, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h1890, h7, h8, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1905 | h1905
        · linarith only [h1745, h1887, h1905, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1907 | h1907
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1908 | h1908
            · linarith only [h1, h1908, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1910 | h1910
              · linarith only [h1745, h1747, h1887, h1907, h1910, h5, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1912 | h1912
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1913 | h1913
                  · linarith only [h1913, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1915 | h1915
                    · linarith only [h1745, h1915, h5, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1917 | h1917
                      · linarith only [h1745, h1887, h1917, h5, hc12, hc34, hlam, hphi, ht23]
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
                          linarith only [h1887, h1912, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          rcases p1919_3 (m.d 0 1) (by simp) with h1922 | h1922
                          · rcases p1919_3 (m.d 0 2) (by simp) with h1923 | h1923
                            · linarith only [h0, h1923, hlam]
                            · linarith only [h1923, h4, hlam]
                          · linarith only [h1, h1922, hlam]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          rcases p1919_3 (m.d 0 1) (by simp) with h1927 | h1927
                          · rcases p1919_3 (m.d 0 2) (by simp) with h1928 | h1928
                            · linarith only [h0, h1928, hlam]
                            · linarith only [h1928, h5, hlam]
                          · linarith only [h1927, h2, hlam]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          rcases p1919_3 (m.d 0 1) (by simp) with h1932 | h1932
                          · rcases p1919_3 (m.d 0 2) (by simp) with h1933 | h1933
                            · linarith only [h0, h1933, hlam]
                            · linarith only [h1933, h6, hlam]
                          · linarith only [h1932, h3, hlam]
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
                          rcases p1919_3 (m.d 0 1) (by simp) with h1939 | h1939
                          · rcases p1919_3 (m.d 0 2) (by simp) with h1940 | h1940
                            · rcases p1919_3 (m.d 0 3) (by simp) with h1941 | h1941
                              · linarith only [h1941, h4, hlam]
                              · rcases p1919_3 (m.d 0 4) (by simp) with h1943 | h1943
                                · linarith only [h1943, h5, hlam]
                                · rcases p1919_3 (m.d 0 5) (by simp) with h1945 | h1945
                                  · linarith only [h1945, h6, hlam]
                                  · linarith only [h1945, h8, hlam]
                            · linarith only [h1940, h4, hlam]
                          · linarith only [h1, h1939, hlam]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          rcases p1919_3 (m.d 0 1) (by simp) with h1950 | h1950
                          · rcases p1919_3 (m.d 0 2) (by simp) with h1951 | h1951
                            · rcases p1919_3 (m.d 0 3) (by simp) with h1952 | h1952
                              · linarith only [h1952, h4, hlam]
                              · linarith only [h1952, h7, hlam]
                            · linarith only [h1951, h5, hlam]
                          · linarith only [h1950, h2, hlam]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          rcases p1919_3 (m.d 0 1) (by simp) with h1957 | h1957
                          · rcases p1919_3 (m.d 0 2) (by simp) with h1958 | h1958
                            · rcases p1919_3 (m.d 0 3) (by simp) with h1959 | h1959
                              · linarith only [h1959, h4, hlam]
                              · rcases p1919_3 (m.d 0 4) (by simp) with h1961 | h1961
                                · linarith only [h1961, h5, hlam]
                                · rcases p1919_3 (m.d 0 5) (by simp) with h1963 | h1963
                                  · linarith only [h1963, h6, hlam]
                                  · rcases h2bigk with h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1887, h1912, h1913, h6, hlam, p1919_1, p1965_2]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h1968 | h1968
                                      · rcases p1965_3 (m.d 1 2) (by simp) with h1969 | h1969
                                        · linarith only [h0, h1969, hlam]
                                        · rcases p1965_3 (m.d 2 3) (by simp) with h1971 | h1971
                                          · linarith only [h1971, hlam, p1965_0]
                                          · rcases p1965_3 (m.d 2 4) (by simp) with h1973 | h1973
                                            · linarith only [h1973, h5, hlam]
                                            · rcases p1965_3 (m.d 2 5) (by simp) with h1975 | h1975
                                              · linarith only [h1975, h6, hlam]
                                              · linarith only [h1913, h1975, hlam]
                                      · linarith only [h1968, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h1979 | h1979
                                      · rcases p1965_3 (m.d 1 2) (by simp) with h1980 | h1980
                                        · linarith only [h0, h1980, hlam]
                                        · rcases p1965_3 (m.d 2 3) (by simp) with h1982 | h1982
                                          · linarith only [h1982, h4, hlam]
                                          · linarith only [h1912, h1982, hlam]
                                      · linarith only [h1979, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h1986 | h1986
                                      · rcases p1965_3 (m.d 1 2) (by simp) with h1987 | h1987
                                        · linarith only [h0, h1987, hlam]
                                        · rcases p1965_3 (m.d 2 3) (by simp) with h1989 | h1989
                                          · linarith only [h1989, h4, hlam]
                                          · rcases p1965_3 (m.d 2 4) (by simp) with h1991 | h1991
                                            · linarith only [h1991, h5, hlam]
                                            · rcases p1965_3 (m.d 2 5) (by simp) with h1993 | h1993
                                              · linarith only [h1993, hlam, p1965_0]
                                              · rcases h3bigk with h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1917, h8, hc13, hc45, hlam, hphi, ht34, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1887, h1912, h1917, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1917, h8, hc34, hc45, hlam, hphi, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h8, hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1, hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1747, hlam, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1, h1917, h8, hc34, hc45, hlam, hphi, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1908, hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h4, hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h0, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1919_1, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h0, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1919_1, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1913, hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h7, hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1907, hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1912, hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [hlam, p1995_0]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1917, hlam, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1917, h7, hc34, hc45, hlam, hphi, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1907, h1917, hc34, hc45, hlam, hphi, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [h1747, h1917, hc12, hc45, hlam, hphi, ht23, ht34, p1995_1]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  rcases p1995_3 (m.d 0 3) (by simp) with h2019 | h2019
                                                  · linarith only [h2019, h8, hlam]
                                                  · linarith only [h2019, h7, hlam]
                                                · have p1995_0 := h1995c.1
                                                  have p1995_1 := h1995c.2.1
                                                  have p1995_2 := h1995c.2.2.1
                                                  have p1995_3 := h1995c.2.2.2
                                                  linarith only [hlam, p1995_0]
                                      · linarith only [h1986, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h0, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1747, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1887, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1905, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h4, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1917, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h0, h1887, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1913, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h5, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h0, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1912, hlam, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1915, hlam, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h6, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1919_1, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h0, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1919_1, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                            · linarith only [h1958, h6, hlam]
                          · linarith only [h1957, h3, hlam]
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
                          linarith only [h1917, h2, h8, hc14, hc45, hlam, hphi, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h8, hlam, p1919_1]
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
                          linarith only [h1745, hlam, p1919_0]
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
                          linarith only [h1, h1907, h1917, h8, hc34, hc45, hlam, hphi, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1887, h1917, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [hlam, p1919_0]
                · linarith only [h1, h1747, h1907, h1912, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1907, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8

set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2063 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h2064 | h2064
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2065 | h2065
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2066 | h2066
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2067 | h2067
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2068 | h2068
          · linarith only [h2063, h2068, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2070 | h2070
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2071 | h2071
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2072 | h2072
                · linarith only [h1, h2070, h2072, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2074 | h2074
                  · linarith only [h0, h2066, h2072, h2074, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h1, h2070, h2074, h7, hc23, hc34, hlam, hphi]
              · linarith only [h2064, h2068, h2070, h2071, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h2063, h2070, h7, hc13, hc34, hlam, hphi]
        · linarith only [h2063, h2065, h2067, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2080 | h2080
        · linarith only [h2066, h2080, h5, hc02, hlam, hphi, ht0b, ht5b, u5ehi2]
        · linarith only [h2063, h2065, h2080, h6, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2083 | h2083
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2084 | h2084
        · linarith only [h0, h2065, h2084, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2086 | h2086
          · linarith only [h2065, h2086, h4, h7, hlam]
          · linarith only [h2065, h2083, h2086, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2089 | h2089
        · linarith only [h0, h2083, h2089, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2091 | h2091
          · linarith only [h1, h2063, h2091, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2093 | h2093
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2094 | h2094
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2095 | h2095
                · linarith only [h2095, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2097 | h2097
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2098 | h2098
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2099 | h2099
                      · rcases h0bigk with h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2065, h2093, h2099, h4, hc01, hlam, hphi, ht0b, ht5b, p2100_1, u5ehi4]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2065, h2093, h2099, h4, hc01, hlam, hphi, ht0b, ht5b, p2100_1, u5ehi4]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2065, h2093, h2099, h4, h7, hc01, hlam, hphi, ht0b, ht5b, p2100_1, u5ehi4]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          rcases p2100_3 (m.d 0 1) (by simp) with h2105 | h2105
                          · rcases p2100_3 (m.d 0 2) (by simp) with h2106 | h2106
                            · linarith only [h0, h2106, hlam]
                            · linarith only [h2106, h6, hlam]
                          · linarith only [h2105, h3, hlam]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h0, hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2065, h2093, h2099, h4, hc02, hlam, hphi, ht0b, ht5b, p2100_1, u5ehi4]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h0, h2065, h2093, h2099, h4, h7, hc01, hlam, hphi, ht0b, ht5b, p2100_1, u5ehi4]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          rcases p2100_3 (m.d 0 1) (by simp) with h2114 | h2114
                          · rcases p2100_3 (m.d 0 2) (by simp) with h2115 | h2115
                            · rcases p2100_3 (m.d 0 3) (by simp) with h2116 | h2116
                              · linarith only [h2116, h4, hlam]
                              · linarith only [h2063, h2116, hlam]
                            · linarith only [h2115, h6, hlam]
                          · linarith only [h2114, h3, hlam]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h1, hlam, p2100_1]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h4, hlam, p2100_1]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h7, hlam, p2100_1]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2089, h6, h7, hc12, hc34, hlam, hphi, ht23, p2100_1]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2, hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h5, hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2065, h2093, h2099, h4, hc04, hlam, hphi, ht0b, ht5b, p2100_1, u5ehi4]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2089, h6, h7, hc12, hc34, hlam, hphi, ht23, p2100_1]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h3, hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h6, hlam, p2100_1]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2063, hlam, p2100_0]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [h2064, hlam, p2100_1]
                        · have p2100_0 := h2100c.1
                          have p2100_1 := h2100c.2.1
                          have p2100_2 := h2100c.2.2.1
                          have p2100_3 := h2100c.2.2.2
                          linarith only [hlam, p2100_0]
                      · linarith only [h2065, h2093, h2099, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · linarith only [h2083, h2091, h2093, h2094, h2098, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h2065, h2093, h2097, hlam]
              · linarith only [h2064, h2091, h2093, h2094, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h2063, h2093, h7, hc13, hc34, hlam, hphi]
  · linarith only [h2063, h2064, h7, hlam]

end R2N4
