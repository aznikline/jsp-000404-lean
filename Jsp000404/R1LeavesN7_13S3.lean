import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h1755 | h1755
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1756 | h1756
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1757 | h1757
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1758 | h1758
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1759 | h1759
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1760 | h1760
            · linarith only [h1, h1755, h1760, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1762 | h1762
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1763 | h1763
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1764 | h1764
                  · linarith only [h1, h1757, h1762, h1764, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1766 | h1766
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1767 | h1767
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1768 | h1768
                        · rcases h2bigk with h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h0, h1758, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h0, h1766, h1768, hc01, hc45, hlam, hphi, ht0b, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h0, h1764, h1766, h1768, hc01, hc45, hlam, hphi, ht0b, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            rcases p1769_3 (m.d 0 2) (by simp) with h1774 | h1774
                            · rcases p1769_3 (m.d 1 2) (by simp) with h1775 | h1775
                              · linarith only [h0, h1775, hlam]
                              · linarith only [h1759, h1775, hlam]
                            · linarith only [h1774, hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h0, hlam, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1766, h1768, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h0, h1764, h1766, h1768, hc01, hc45, hlam, hphi, ht0b, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h4, hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1757, hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1764, hlam, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1, h1757, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h5, hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1758, hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1766, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h0, h1758, h1766, h1768, hc01, hc45, hlam, hphi, ht0b, ht5b, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h6, hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1759, hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1766, hlam, p1769_0]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [h1767, hlam, p1769_1]
                          · have p1769_0 := h1769c.1
                            have p1769_1 := h1769c.2.1
                            have p1769_2 := h1769c.2.2.1
                            have p1769_3 := h1769c.2.2.2
                            linarith only [hlam, p1769_0]
                        · linarith only [h1756, h1766, h1768, h2, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h1758, h1763, h1764, h1766, h1767, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1755, h1766, h7, hc23, hc34, hlam, hphi]
                · linarith only [h1760, h1762, h1763, hlam]
              · linarith only [h1755, h1762, h7, hc13, hc34, hlam, hphi]
          · linarith only [h1755, h1757, h1759, h6, h7, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1805 | h1805
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1806 | h1806
            · linarith only [h1, h1755, h1806, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1808 | h1808
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1809 | h1809
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1810 | h1810
                  · linarith only [h1757, h1758, h1810, h5, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1812 | h1812
                    · linarith only [h0, h1757, h1758, h1812, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1, h1808, h1812, h7, hc23, hc34, hlam, hphi]
                · linarith only [h1756, h1757, h1758, h1809, h7, hc23, hc34, hlam, hphi]
              · linarith only [h1755, h1808, h7, hc13, hc34, hlam, hphi]
          · linarith only [h1755, h1757, h1805, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1818 | h1818
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1819 | h1819
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1820 | h1820
            · linarith only [h1757, h1820, h4, h7, hlam]
            · linarith only [h1757, h1818, h1820, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1823 | h1823
            · linarith only [h1755, h1818, h1819, h1823, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1757, h1818, h1823, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1826 | h1826
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1827 | h1827
            · linarith only [h1, h1755, h1827, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1829 | h1829
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1830 | h1830
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1831 | h1831
                  · linarith only [h1831, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1833 | h1833
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1834 | h1834
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1835 | h1835
                        · rcases h2bigk with h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1826, h1833, h1835, hc02, hc45, hlam, hphi, ht0b, ht5b, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h0, h1757, h1826, h1833, h1835, hc01, hc45, hlam, hphi, ht0b, ht5b, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h0, h1757, h1826, h1831, h1833, h1835, hc01, hc45, hlam, hphi, ht0b, ht5b, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            rcases p1836_3 (m.d 0 2) (by simp) with h1841 | h1841
                            · rcases p1836_3 (m.d 1 2) (by simp) with h1842 | h1842
                              · linarith only [h0, h1842, hlam]
                              · linarith only [h1826, h1842, hlam]
                            · linarith only [h1841, hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h0, hlam, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1757, hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1818, hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1757, h1833, h1835, h4, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h4, hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1831, hlam, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1833, h1835, h4, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h5, hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1826, h1833, h1835, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h0, h1833, h1835, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h6, hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1826, hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1833, hlam, p1836_0]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [h1834, hlam, p1836_1]
                          · have p1836_0 := h1836c.1
                            have p1836_1 := h1836c.2.1
                            have p1836_2 := h1836c.2.2.1
                            have p1836_3 := h1836c.2.2.2
                            linarith only [hlam, p1836_0]
                        · linarith only [h1757, h1826, h1833, h1835, h4, h7, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h1818, h1826, h1830, h1833, h1834, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h1755, h1757, h1826, h1833, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h1818, h1826, h1830, hlam]
              · linarith only [h1755, h1757, h1826, h1829, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1871 | h1871
            · linarith only [h1, h1755, h1871, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1873 | h1873
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1874 | h1874
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1875 | h1875
                  · linarith only [h1875, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1877 | h1877
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1878 | h1878
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1879 | h1879
                        · rcases h2bigk with h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            rcases p1880_3 (m.d 0 2) (by simp) with h1882 | h1882
                            · rcases p1880_3 (m.d 1 2) (by simp) with h1883 | h1883
                              · linarith only [h0, h1883, hlam]
                              · rcases p1880_3 (m.d 2 3) (by simp) with h1885 | h1885
                                · linarith only [h1885, h4, hlam]
                                · linarith only [h1757, h1885, hlam]
                            · linarith only [h0, h1882, hlam]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h0, h1757, h1873, hc01, hc35, hlam, hphi, ht0b, ht5b, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h0, h1818, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h0, h1826, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h0, hlam, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h1757, hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h1818, hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h1826, hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h4, hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h1875, hlam, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h1826, hc12, hc23, hlam, hphi, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h5, hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h0, h1826, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h6, hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h1877, hc12, hc23, hlam, hphi, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h1877, hlam, p1880_0]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [h1878, hlam, p1880_1]
                          · have p1880_0 := h1880c.1
                            have p1880_1 := h1880c.2.1
                            have p1880_2 := h1880c.2.2.1
                            have p1880_3 := h1880c.2.2.2
                            linarith only [hlam, p1880_0]
                        · linarith only [h1, h1756, h1873, h1879, h7, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1757, h1818, h1873, h1874, h1878, h4, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1755, h1757, h1877, h7, hc13, hc34, hlam, hphi]
                · linarith only [h1871, h1873, h1874, hlam]
              · linarith only [h1755, h1873, h7, hc13, hc34, hlam, hphi]
    · linarith only [h1755, h1756, h7, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1918 | h1918
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1919 | h1919
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1920 | h1920
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1921 | h1921
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1922 | h1922
            · linarith only [h1, h1922, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1924 | h1924
              · linarith only [h1, h1755, h1924, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1926 | h1926
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1927 | h1927
                  · linarith only [h1, h1919, h1927, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1929 | h1929
                    · linarith only [h1, h1755, h1919, h1929, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1931 | h1931
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1932 | h1932
                        · rcases h2bigk with h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h0, h1920, h1931, hc01, hc45, hlam, hphi, ht0b, ht5b, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            rcases p1933_3 (m.d 0 2) (by simp) with h1936 | h1936
                            · rcases p1933_3 (m.d 1 2) (by simp) with h1937 | h1937
                              · linarith only [h0, h1937, hlam]
                              · linarith only [h1919, h1937, hlam]
                            · linarith only [h1936, hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h0, h1931, hc01, hc45, hlam, hphi, ht0b, ht5b, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            rcases p1933_3 (m.d 0 2) (by simp) with h1942 | h1942
                            · rcases p1933_3 (m.d 1 2) (by simp) with h1943 | h1943
                              · linarith only [h0, h1943, hlam]
                              · linarith only [h1921, h1943, hlam]
                            · linarith only [h1942, hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h0, hlam, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h0, h1931, hc01, hc45, hlam, hphi, ht0b, ht5b, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h0, h1929, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h4, hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h1919, hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h1927, hlam, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h1929, hlam, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h5, hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h1920, hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h1920, h1929, h2, h7, hc23, hc34, hlam, hphi, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h6, hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h1921, hlam, p1933_0]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [h1931, hlam, p1933_1]
                          · have p1933_0 := h1933c.1
                            have p1933_1 := h1933c.2.1
                            have p1933_2 := h1933c.2.2.1
                            have p1933_3 := h1933c.2.2.2
                            linarith only [hlam, p1933_0]
                        · linarith only [h1918, h1932, h7, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1968 | h1968
                        · rcases h2bigk with h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h0, h1919, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            rcases p1969_3 (m.d 0 2) (by simp) with h1972 | h1972
                            · rcases p1969_3 (m.d 1 2) (by simp) with h1973 | h1973
                              · linarith only [h0, h1973, hlam]
                              · linarith only [h1919, h1973, hlam]
                            · linarith only [h1972, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            rcases p1969_3 (m.d 0 2) (by simp) with h1977 | h1977
                            · rcases p1969_3 (m.d 1 2) (by simp) with h1978 | h1978
                              · linarith only [h0, h1978, hlam]
                              · linarith only [h1920, h1978, hlam]
                            · linarith only [h1977, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            rcases p1969_3 (m.d 0 2) (by simp) with h1982 | h1982
                            · rcases p1969_3 (m.d 1 2) (by simp) with h1983 | h1983
                              · linarith only [h0, h1983, hlam]
                              · linarith only [h1921, h1983, hlam]
                            · linarith only [h1982, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h0, hlam, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h0, h1927, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h4, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h1919, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h1927, hlam, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h1929, hlam, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h5, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h1920, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h1926, h1931, h2, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h1931, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h6, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h1921, hlam, p1969_0]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [h0, h1920, h1926, h1931, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1969_1]
                          · have p1969_0 := h1969c.1
                            have p1969_1 := h1969c.2.1
                            have p1969_2 := h1969c.2.2.1
                            have p1969_3 := h1969c.2.2.2
                            linarith only [hlam, p1969_0]
                        · linarith only [h1926, h1968, h2, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2008 | h2008
                  · linarith only [h1, h1918, h1919, h1926, h2008, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2010 | h2010
                    · linarith only [h1755, h1918, h1919, h1922, h1926, h2010, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2012 | h2012
                      · linarith only [h0, h1920, h1922, h1926, h2012, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2014 | h2014
                        · rcases h2bigk with h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c | h2015c
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h0, h1919, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            rcases p2015_3 (m.d 0 2) (by simp) with h2018 | h2018
                            · rcases p2015_3 (m.d 1 2) (by simp) with h2019 | h2019
                              · linarith only [h0, h2019, hlam]
                              · linarith only [h1919, h2019, hlam]
                            · linarith only [h2018, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            rcases p2015_3 (m.d 0 2) (by simp) with h2023 | h2023
                            · rcases p2015_3 (m.d 1 2) (by simp) with h2024 | h2024
                              · linarith only [h0, h2024, hlam]
                              · linarith only [h1920, h2024, hlam]
                            · linarith only [h2023, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            rcases p2015_3 (m.d 0 2) (by simp) with h2028 | h2028
                            · rcases p2015_3 (m.d 1 2) (by simp) with h2029 | h2029
                              · linarith only [h0, h2029, hlam]
                              · linarith only [h1921, h2029, hlam]
                            · linarith only [h2028, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h0, hlam, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h0, h2008, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h0, h2008, h2012, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h4, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h1919, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h2008, hlam, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h2010, hlam, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h5, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h1920, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h2012, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h6, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h1921, hlam, p2015_0]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h1918, h1921, h1926, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [h1918, h1921, h1926, h7, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2015_1]
                          · have p2015_0 := h2015c.1
                            have p2015_1 := h2015c.2.1
                            have p2015_2 := h2015c.2.2.1
                            have p2015_3 := h2015c.2.2.2
                            linarith only [hlam, p2015_0]
                        · linarith only [h1918, h2014, h7, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2054 | h2054
            · linarith only [h1, h2054, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2056 | h2056
              · linarith only [h1, h1755, h2056, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2058 | h2058
                · linarith only [h1920, h1921, h2058, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2060 | h2060
                  · linarith only [h1918, h1919, h1921, h2058, h2060, h6, h7, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2062 | h2062
                    · linarith only [h1755, h1920, h1921, h2060, h2062, h6, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2064 | h2064
                      · linarith only [h1920, h1921, h2058, h2064, hlam]
                      · linarith only [h1918, h1920, h1921, h2060, h2064, h7, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2067 | h2067
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2068 | h2068
            · linarith only [h1, h1755, h1919, h1920, h2, h2068, h7, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2070 | h2070
              · linarith only [h1, h1755, h2070, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2072 | h2072
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2073 | h2073
                  · linarith only [h1, h1755, h1919, h1920, h2073, h5, h7, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2075 | h2075
                    · linarith only [h1755, h1919, h1920, h2075, h5, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2077 | h2077
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2078 | h2078
                        · rcases h2bigk with h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h0, h1919, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            rcases p2079_3 (m.d 0 2) (by simp) with h2082 | h2082
                            · rcases p2079_3 (m.d 1 2) (by simp) with h2083 | h2083
                              · linarith only [h0, h2083, hlam]
                              · linarith only [h1919, h2083, hlam]
                            · linarith only [h2082, hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h0, h1920, h2067, h2075, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            rcases p2079_3 (m.d 0 2) (by simp) with h2088 | h2088
                            · rcases p2079_3 (m.d 1 2) (by simp) with h2089 | h2089
                              · linarith only [h0, h2089, hlam]
                              · linarith only [h2067, h2089, hlam]
                            · linarith only [h2088, hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h0, hlam, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h1920, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h1920, hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h0, h1920, h2075, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h4, hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h1919, hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h2073, hlam, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h2075, hlam, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h5, hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h0, h2075, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h6, hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h2067, hlam, p2079_0]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h2067, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [h2077, hlam, p2079_1]
                          · have p2079_0 := h2079c.1
                            have p2079_1 := h2079c.2.1
                            have p2079_2 := h2079c.2.2.1
                            have p2079_3 := h2079c.2.2.2
                            linarith only [hlam, p2079_0]
                        · linarith only [h1918, h2078, h7, hlam]
                      · linarith only [h1920, h2067, h2072, h2077, hlam]
                · linarith only [h1918, h1919, h1920, h2072, h7, hc23, hc34, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2116 | h2116
            · linarith only [h1, h1919, h1920, h2116, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2118 | h2118
              · linarith only [h1, h1755, h2118, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2120 | h2120
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2121 | h2121
                  · linarith only [h0, h1919, h1920, h2121, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2123 | h2123
                    · linarith only [h0, h1755, h1919, h1920, h2123, h5, hc01, hc05, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2125 | h2125
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2126 | h2126
                        · rcases h2bigk with h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h0, h1919, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            rcases p2127_3 (m.d 0 2) (by simp) with h2130 | h2130
                            · rcases p2127_3 (m.d 1 2) (by simp) with h2131 | h2131
                              · linarith only [h0, h2131, hlam]
                              · linarith only [h1919, h2131, hlam]
                            · linarith only [h2130, hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h0, h1919, h1920, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h0, h1919, h2067, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h0, hlam, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h1920, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h1920, hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h2067, hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h4, hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h1919, hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h2121, hlam, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h2123, hlam, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h5, hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h0, h1919, h2067, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h6, hlam, p2127_0]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h1919, h6, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [h2125, hlam, p2127_1]
                          · have p2127_0 := h2127c.1
                            have p2127_1 := h2127c.2.1
                            have p2127_2 := h2127c.2.2.1
                            have p2127_3 := h2127c.2.2.2
                            linarith only [hlam, p2127_0]
                        · linarith only [h1918, h2126, h7, hlam]
                      · linarith only [h1919, h1920, h2120, h2125, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h1918, h1919, h1920, h2120, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2160 | h2160
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2161 | h2161
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2162 | h2162
            · linarith only [h1919, h2160, h2162, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1919, h2160, h2162, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2165 | h2165
            · linarith only [h1919, h2160, h2165, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1919, h2160, h2165, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2168 | h2168
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2169 | h2169
            · linarith only [h1919, h2168, h2169, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2171 | h2171
              · linarith only [h1755, h1919, h2171, h4, hlam]
              · linarith only [h1919, h2168, h2171, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2174 | h2174
            · linarith only [h1, h1919, h2174, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2176 | h2176
              · linarith only [h1755, h1919, h2176, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2178 | h2178
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2179 | h2179
                  · linarith only [h2179, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2181 | h2181
                    · linarith only [h1755, h2181, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2183 | h2183
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2184 | h2184
                        · rcases h2bigk with h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c | h2185c
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            rcases p2185_3 (m.d 0 2) (by simp) with h2187 | h2187
                            · rcases p2185_3 (m.d 1 2) (by simp) with h2188 | h2188
                              · linarith only [h0, h2188, hlam]
                              · rcases p2185_3 (m.d 2 3) (by simp) with h2190 | h2190
                                · linarith only [h2190, h4, hlam]
                                · linarith only [h1919, h2190, hlam]
                            · linarith only [h0, h2187, hlam]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h1919, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h0, h2160, h2178, hc01, hc45, hlam, hphi, ht0b, ht5b, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h0, h2168, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h0, hlam, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h1919, hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h2160, hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h2168, hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h4, hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h2179, hlam, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h2181, hlam, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h5, hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h0, h1919, h2181, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h6, hlam, p2185_0]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h0, h1919, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [h2183, hlam, p2185_1]
                          · have p2185_0 := h2185c.1
                            have p2185_1 := h2185c.2.1
                            have p2185_2 := h2185c.2.2.1
                            have p2185_3 := h2185c.2.2.2
                            linarith only [hlam, p2185_0]
                        · linarith only [h1919, h2184, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h2160, h2178, h2183, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2219 | h2219
                  · linarith only [h1918, h1919, h2174, h2178, h2219, h7, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2221 | h2221
                    · linarith only [h1755, h2221, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2223 | h2223
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2224 | h2224
                        · rcases h2bigk with h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c | h2225c
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            rcases p2225_3 (m.d 0 2) (by simp) with h2227 | h2227
                            · rcases p2225_3 (m.d 1 2) (by simp) with h2228 | h2228
                              · linarith only [h0, h2228, hlam]
                              · rcases p2225_3 (m.d 2 3) (by simp) with h2230 | h2230
                                · linarith only [h2230, h4, hlam]
                                · linarith only [h1919, h2230, hlam]
                            · linarith only [h0, h2227, hlam]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h0, h1919, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h0, h1919, h2174, h2178, h2223, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h0, h1919, h2221, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h0, hlam, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h1919, hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h2160, hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h2168, hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h4, hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h2219, hlam, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h2221, hlam, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h5, hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h0, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h6, hlam, p2225_0]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h1919, h6, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [h2223, hlam, p2225_1]
                          · have p2225_0 := h2225c.1
                            have p2225_1 := h2225c.2.1
                            have p2225_2 := h2225c.2.2.1
                            have p2225_3 := h2225c.2.2.2
                            linarith only [hlam, p2225_0]
                        · linarith only [h1919, h2224, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1918, h2160, h2223, h7, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2259 | h2259
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2260 | h2260
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2261 | h2261
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2262 | h2262
            · linarith only [h1, h2262, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2264 | h2264
              · linarith only [h1, h1755, h2264, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2266 | h2266
                · linarith only [h1918, h2, h2266, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2268 | h2268
                  · linarith only [h2268, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2270 | h2270
                    · linarith only [h1, h1755, h2259, h2270, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2272 | h2272
                      · linarith only [h1918, h2, h2260, h2272, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2274 | h2274
                        · rcases h2bigk with h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h0, h2259, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            rcases p2275_3 (m.d 0 2) (by simp) with h2278 | h2278
                            · rcases p2275_3 (m.d 1 2) (by simp) with h2279 | h2279
                              · linarith only [h0, h2279, hlam]
                              · linarith only [h2259, h2279, hlam]
                            · linarith only [h2278, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            rcases p2275_3 (m.d 0 2) (by simp) with h2283 | h2283
                            · rcases p2275_3 (m.d 1 2) (by simp) with h2284 | h2284
                              · linarith only [h0, h2284, hlam]
                              · linarith only [h2260, h2284, hlam]
                            · linarith only [h2283, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            rcases p2275_3 (m.d 0 2) (by simp) with h2288 | h2288
                            · rcases p2275_3 (m.d 1 2) (by simp) with h2289 | h2289
                              · linarith only [h0, h2289, hlam]
                              · linarith only [h2261, h2289, hlam]
                            · linarith only [h2288, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h0, hlam, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h4, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h2259, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h2268, hlam, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h2270, hlam, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h5, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h2260, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h2272, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h6, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h2261, hlam, p2275_0]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [h2261, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2275_1]
                          · have p2275_0 := h2275c.1
                            have p2275_1 := h2275c.2.1
                            have p2275_2 := h2275c.2.2.1
                            have p2275_3 := h2275c.2.2.2
                            linarith only [hlam, p2275_0]
                        · rcases h2bigk with h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h0, h2259, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            rcases p2313_3 (m.d 0 2) (by simp) with h2316 | h2316
                            · rcases p2313_3 (m.d 1 2) (by simp) with h2317 | h2317
                              · linarith only [h0, h2317, hlam]
                              · linarith only [h2259, h2317, hlam]
                            · linarith only [h2316, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            rcases p2313_3 (m.d 0 2) (by simp) with h2321 | h2321
                            · rcases p2313_3 (m.d 1 2) (by simp) with h2322 | h2322
                              · linarith only [h0, h2322, hlam]
                              · linarith only [h2260, h2322, hlam]
                            · linarith only [h2321, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            rcases p2313_3 (m.d 0 2) (by simp) with h2326 | h2326
                            · rcases p2313_3 (m.d 1 2) (by simp) with h2327 | h2327
                              · linarith only [h0, h2327, hlam]
                              · linarith only [h2261, h2327, hlam]
                            · linarith only [h2326, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h0, hlam, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h0, h2268, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h4, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h2259, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h2268, hlam, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h2270, hlam, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h5, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h2260, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h2272, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h6, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h2261, hlam, p2313_0]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [h2261, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2313_1]
                          · have p2313_0 := h2313c.1
                            have p2313_1 := h2313c.2.1
                            have p2313_2 := h2313c.2.2.1
                            have p2313_3 := h2313c.2.2.2
                            linarith only [hlam, p2313_0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2351 | h2351
            · linarith only [h1, h2351, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2353 | h2353
              · linarith only [h1, h1755, h2353, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2355 | h2355
                · linarith only [h0, h1918, h2260, h2261, h2355, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2357 | h2357
                  · linarith only [h2259, h2261, h2357, h6, h7, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2359 | h2359
                    · linarith only [h1, h1755, h2259, h2359, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2361 | h2361
                      · linarith only [h0, h1918, h2260, h2261, h2361, h6, hc01, hc05, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2363 | h2363
                        · linarith only [h1918, h2259, h2261, h2363, h6, hc23, hc34, hlam, hphi]
                        · rcases h2bigk with h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, h2260, h2357, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            rcases p2365_3 (m.d 0 2) (by simp) with h2368 | h2368
                            · rcases p2365_3 (m.d 1 2) (by simp) with h2369 | h2369
                              · linarith only [h0, h2369, hlam]
                              · linarith only [h2259, h2369, hlam]
                            · linarith only [h2368, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            rcases p2365_3 (m.d 0 2) (by simp) with h2373 | h2373
                            · rcases p2365_3 (m.d 1 2) (by simp) with h2374 | h2374
                              · linarith only [h0, h2374, hlam]
                              · linarith only [h2260, h2374, hlam]
                            · linarith only [h2373, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, h2260, h2261, h2357, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, hlam, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2261, h6, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, h2261, h2357, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2261, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h4, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2259, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2357, hlam, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2359, hlam, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h5, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2260, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2361, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h6, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, h2357, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
        · linarith only [h1918, h2259, h2260, h5, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2400 | h2400
        · linarith only [h1918, h2259, h2400, h4, h7, hc24, hc45, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2402 | h2402
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2403 | h2403
            · linarith only [h2259, h2403, h4, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2405 | h2405
              · linarith only [h1755, h2259, h2402, h2405, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h2259, h2402, h2405, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2408 | h2408
            · linarith only [h1, h2259, h2408, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2410 | h2410
              · linarith only [h1755, h2259, h2410, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2412 | h2412
                · linarith only [h1918, h2400, h2412, h5, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2414 | h2414
                  · linarith only [h2414, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2416 | h2416
                    · linarith only [h1755, h2416, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2418 | h2418
                      · linarith only [h1918, h2418, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2420 | h2420
                        · linarith only [h1918, h2259, h2420, h4, h7, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h2259, h2420, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7

set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h2423 | h2423
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2424 | h2424
    · linarith only [h2424, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2426 | h2426
      · linarith only [h2423, h2426, h4, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2428 | h2428
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2429 | h2429
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2430 | h2430
            · linarith only [h0, h2430, h6, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2432 | h2432
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2433 | h2433
                · linarith only [h1, h2424, h2433, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2435 | h2435
                  · linarith only [h2, h2423, h2426, h2435, h4, h6, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2437 | h2437
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2438 | h2438
                      · linarith only [h0, h1, h2424, h2428, h2438, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2440 | h2440
                        · linarith only [h2426, h2437, h2440, h4, h6, hlam]
                        · linarith only [h0, h2428, h2437, h2440, h6, hc34, hc45, hlam, hphi]
                    · linarith only [h2423, h2424, h2437, hc23, hc35, hlam, hphi]
              · linarith only [h2423, h2424, h2432, hc13, hc35, hlam, hphi]
          · linarith only [h2429, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h2428, h4, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2447 | h2447
    · linarith only [h2447, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2449 | h2449
      · linarith only [h2449, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2451 | h2451
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2452 | h2452
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2453 | h2453
            · linarith only [h0, h2453, h6, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2455 | h2455
              · linarith only [h1, h2423, h2455, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2457 | h2457
                · linarith only [h1, h2447, h2457, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2459 | h2459
                  · linarith only [h2, h2449, h2459, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2461 | h2461
                    · linarith only [h1, h2423, h2461, h4, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2463 | h2463
                      · linarith only [h2447, h2463, h4, h6, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2465 | h2465
                        · linarith only [h0, h1, h2423, h2449, h2452, h2465, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2467 | h2467
                          · linarith only [h2465, h2467, h4, h6, hc23, hc34, hlam, hphi]
                          · rcases h2bigk with h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2452, h2461, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2461, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h6, hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h0, hlam, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h0, h2461, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2453, hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h4, hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2451, hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2461, hlam, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2463, hlam, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h5, hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2452, hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h5, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2465, hlam, p2469_0]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [hc02, hc25, hlam, hphi, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2451, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2463, h2467, hc23, hc45, hlam, hphi, ht34, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [h2461, h2463, h2467, hc23, hc45, hlam, hphi, ht34, p2469_1]
                            · have p2469_0 := h2469c.1
                              have p2469_1 := h2469c.2.1
                              have p2469_2 := h2469c.2.2.1
                              have p2469_3 := h2469c.2.2.2
                              linarith only [hlam, p2469_0]
          · linarith only [h2452, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h2451, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6

end R2N4
