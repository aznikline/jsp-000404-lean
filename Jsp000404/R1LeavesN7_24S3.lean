import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1616 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h1796 | h1796
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1797 | h1797
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1798 | h1798
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1799 | h1799
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1800 | h1800
          · linarith only [h1, h1800, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1802 | h1802
            · linarith only [h1, h1616, h1802, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1804 | h1804
              · linarith only [h1, h1797, h1804, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1806 | h1806
                · linarith only [h1, h1616, h1797, h1806, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1808 | h1808
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1809 | h1809
                    · rcases h0bigk with h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [hlam, p1810_0]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h0, h1798, h1808, hc01, hc45, hlam, hphi, ht0b, ht5b, p1810_1]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        rcases p1810_3 (m.d 0 1) (by simp) with h1813 | h1813
                        · rcases p1810_3 (m.d 0 2) (by simp) with h1814 | h1814
                          · linarith only [h0, h1814, hlam]
                          · linarith only [h1814, h4, hlam]
                        · linarith only [h1, h1813, hlam]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        rcases p1810_3 (m.d 0 1) (by simp) with h1818 | h1818
                        · rcases p1810_3 (m.d 0 2) (by simp) with h1819 | h1819
                          · linarith only [h0, h1819, hlam]
                          · linarith only [h1819, h5, hlam]
                        · linarith only [h1818, h2, hlam]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        rcases p1810_3 (m.d 0 1) (by simp) with h1823 | h1823
                        · rcases p1810_3 (m.d 0 2) (by simp) with h1824 | h1824
                          · linarith only [h0, h1824, hlam]
                          · linarith only [h1824, h6, hlam]
                        · linarith only [h1823, h3, hlam]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h0, hlam, p1810_0]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [hlam, p1810_0]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        rcases p1810_3 (m.d 0 1) (by simp) with h1830 | h1830
                        · rcases p1810_3 (m.d 0 2) (by simp) with h1831 | h1831
                          · rcases p1810_3 (m.d 0 3) (by simp) with h1832 | h1832
                            · linarith only [h1832, h4, hlam]
                            · rcases p1810_3 (m.d 0 4) (by simp) with h1834 | h1834
                              · linarith only [h1834, h5, hlam]
                              · linarith only [h1834, h7, hlam]
                          · linarith only [h1831, h4, hlam]
                        · linarith only [h1, h1830, hlam]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        rcases p1810_3 (m.d 0 1) (by simp) with h1839 | h1839
                        · rcases p1810_3 (m.d 0 2) (by simp) with h1840 | h1840
                          · rcases p1810_3 (m.d 0 3) (by simp) with h1841 | h1841
                            · linarith only [h1841, h4, hlam]
                            · rcases p1810_3 (m.d 0 4) (by simp) with h1843 | h1843
                              · linarith only [h1843, h5, hlam]
                              · rcases p1810_3 (m.d 0 5) (by simp) with h1845 | h1845
                                · linarith only [h1845, h6, hlam]
                                · rcases h0emin with h1847 | h1847 | h1847 | h1847 | h1847
                                  · rcases h2bigk with h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h1798, h1808, hc02, hc45, hlam, hphi, ht0b, ht5b, p1848_1]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      rcases p1848_3 (m.d 0 2) (by simp) with h1851 | h1851
                                      · rcases p1848_3 (m.d 1 2) (by simp) with h1852 | h1852
                                        · linarith only [h0, h1852, hlam]
                                        · linarith only [h1797, h1852, hlam]
                                      · linarith only [h1851, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      rcases p1848_3 (m.d 0 2) (by simp) with h1856 | h1856
                                      · rcases p1848_3 (m.d 1 2) (by simp) with h1857 | h1857
                                        · linarith only [h0, h1857, hlam]
                                        · linarith only [h1798, h1857, hlam]
                                      · linarith only [h1856, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      rcases p1848_3 (m.d 0 2) (by simp) with h1861 | h1861
                                      · rcases p1848_3 (m.d 1 2) (by simp) with h1862 | h1862
                                        · linarith only [h0, h1862, hlam]
                                        · linarith only [h1799, h1862, hlam]
                                      · linarith only [h1861, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h0, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      rcases p1848_3 (m.d 0 2) (by simp) with h1868 | h1868
                                      · rcases p1848_3 (m.d 1 2) (by simp) with h1869 | h1869
                                        · rcases p1848_3 (m.d 2 3) (by simp) with h1870 | h1870
                                          · linarith only [h1870, hlam, p1848_0]
                                          · rcases p1848_3 (m.d 2 4) (by simp) with h1872 | h1872
                                            · linarith only [h1798, h1872, hlam]
                                            · linarith only [h1804, h1872, hlam]
                                        · linarith only [h1869, hlam, p1848_0]
                                      · linarith only [h1868, h4, hlam]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h0, h1808, hc01, hc45, hlam, hphi, ht0b, ht5b, p1848_1]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      rcases p1848_3 (m.d 0 2) (by simp) with h1878 | h1878
                                      · rcases p1848_3 (m.d 1 2) (by simp) with h1879 | h1879
                                        · rcases p1848_3 (m.d 2 3) (by simp) with h1880 | h1880
                                          · linarith only [h1797, h1880, hlam]
                                          · rcases p1848_3 (m.d 2 4) (by simp) with h1882 | h1882
                                            · linarith only [h1798, h1882, hlam]
                                            · linarith only [h1808, h1882, hlam]
                                        · linarith only [h1879, hlam, p1848_0]
                                      · linarith only [h1878, h6, hlam]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h4, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h1797, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h1804, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h1806, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h5, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h1798, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h0, h1798, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1810_1, p1848_1]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h0, h1798, h1806, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1848_1]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h6, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h1799, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h1616, h6, hc23, hlam, hphi, p1848_1, u3elo4]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [h1808, hlam, p1848_0]
                                    · have p1848_0 := h1848c.1
                                      have p1848_1 := h1848c.2.1
                                      have p1848_2 := h1848c.2.2.1
                                      have p1848_3 := h1848c.2.2.2
                                      linarith only [hlam, p1848_0]
                                  · rcases h2bigk with h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h0, h1798, h1808, hc01, hc45, hlam, hphi, ht0b, ht5b, p1902_1]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      rcases p1902_3 (m.d 0 2) (by simp) with h1905 | h1905
                                      · rcases p1902_3 (m.d 1 2) (by simp) with h1906 | h1906
                                        · linarith only [h0, h1906, hlam]
                                        · linarith only [h1797, h1906, hlam]
                                      · linarith only [h1905, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      rcases p1902_3 (m.d 0 2) (by simp) with h1910 | h1910
                                      · rcases p1902_3 (m.d 1 2) (by simp) with h1911 | h1911
                                        · linarith only [h0, h1911, hlam]
                                        · linarith only [h1798, h1911, hlam]
                                      · linarith only [h1910, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      rcases p1902_3 (m.d 0 2) (by simp) with h1915 | h1915
                                      · rcases p1902_3 (m.d 1 2) (by simp) with h1916 | h1916
                                        · linarith only [h0, h1916, hlam]
                                        · linarith only [h1799, h1916, hlam]
                                      · linarith only [h1915, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h0, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      rcases p1902_3 (m.d 0 2) (by simp) with h1922 | h1922
                                      · rcases p1902_3 (m.d 1 2) (by simp) with h1923 | h1923
                                        · rcases p1902_3 (m.d 2 3) (by simp) with h1924 | h1924
                                          · linarith only [h1924, hlam, p1902_0]
                                          · rcases p1902_3 (m.d 2 4) (by simp) with h1926 | h1926
                                            · linarith only [h1798, h1926, hlam]
                                            · linarith only [h1804, h1926, hlam]
                                        · linarith only [h1923, hlam, p1902_0]
                                      · linarith only [h1922, h4, hlam]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h0, h1808, hc01, hc45, hlam, hphi, ht0b, ht5b, p1902_1]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      rcases p1902_3 (m.d 0 2) (by simp) with h1932 | h1932
                                      · rcases p1902_3 (m.d 1 2) (by simp) with h1933 | h1933
                                        · rcases p1902_3 (m.d 2 3) (by simp) with h1934 | h1934
                                          · linarith only [h1797, h1934, hlam]
                                          · rcases p1902_3 (m.d 2 4) (by simp) with h1936 | h1936
                                            · linarith only [h1798, h1936, hlam]
                                            · linarith only [h1808, h1936, hlam]
                                        · linarith only [h1933, hlam, p1902_0]
                                      · linarith only [h1932, h6, hlam]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h4, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h1797, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h1804, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h1806, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h5, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h1798, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1810_1, p1902_1]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h0, h1798, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1810_1, p1902_1]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h6, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h1799, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h0, h1796, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1810_1, p1902_1]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [h1808, hlam, p1902_0]
                                    · have p1902_0 := h1902c.1
                                      have p1902_1 := h1902c.2.1
                                      have p1902_2 := h1902c.2.2.1
                                      have p1902_3 := h1902c.2.2.2
                                      linarith only [hlam, p1902_0]
                                  · linarith only [h1847, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h0, h1847, hc01, hlam, p1810_1]
                                  · linarith only [h0, h1796, h1847, hc01, hlam, p1810_1]
                          · linarith only [h1840, h5, hlam]
                        · linarith only [h1839, h2, hlam]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        rcases p1810_3 (m.d 0 1) (by simp) with h1961 | h1961
                        · rcases p1810_3 (m.d 0 2) (by simp) with h1962 | h1962
                          · rcases p1810_3 (m.d 0 3) (by simp) with h1963 | h1963
                            · linarith only [h1963, h4, hlam]
                            · rcases p1810_3 (m.d 0 4) (by simp) with h1965 | h1965
                              · linarith only [h1965, h5, hlam]
                              · linarith only [h1796, h1965, hlam]
                          · linarith only [h1962, h6, hlam]
                        · linarith only [h1961, h3, hlam]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h1, hlam, p1810_1]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h4, hlam, p1810_1]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [hlam, p1810_0]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h7, hlam, p1810_1]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h1616, hlam, p1810_1]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h2, hlam, p1810_0]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h5, hlam, p1810_0]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h1, h1797, h7, hc23, hlam, hphi, p1810_1, u3elo3]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [hlam, p1810_0]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h1, h1616, h1797, h7, hc23, hlam, hphi, p1810_1, u3elo3]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h3, hlam, p1810_0]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h6, hlam, p1810_1]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h1, h1616, h1797, h1809, hc23, hlam, hphi, p1810_1, u3elo3]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [h1796, hlam, p1810_1]
                      · have p1810_0 := h1810c.1
                        have p1810_1 := h1810c.2.1
                        have p1810_2 := h1810c.2.2.1
                        have p1810_3 := h1810c.2.2.2
                        linarith only [hlam, p1810_0]
                    · linarith only [h1796, h1809, h7, hlam]
                  · linarith only [h1796, h1804, h1808, h7, hc23, hlam, hphi, u3elo3]
        · linarith only [h1796, h1797, h1799, h6, h7, hc23, hlam, hphi, u3elo3]
      · linarith only [h1797, h1798, h5, h7, hc23, hlam, hphi, u3elo3]
    · linarith only [h1797, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1990 | h1990
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1991 | h1991
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1992 | h1992
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1993 | h1993
          · linarith only [h1, h1993, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1995 | h1995
            · linarith only [h1, h1616, h1796, h1995, h7, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1997 | h1997
              · linarith only [h1, h1990, h1997, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1999 | h1999
                · linarith only [h1, h1616, h1990, h1999, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2001 | h2001
                  · linarith only [h0, h1, h1796, h1990, h1991, h2001, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2003 | h2003
                    · linarith only [h1, h1796, h1990, h2003, h7, hc23, hlam, hphi, u3elo3]
                    · rcases h0bigk with h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c | h2005c
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        rcases p2005_3 (m.d 0 1) (by simp) with h2007 | h2007
                        · rcases p2005_3 (m.d 0 2) (by simp) with h2008 | h2008
                          · linarith only [h0, h2008, hlam]
                          · rcases p2005_3 (m.d 0 3) (by simp) with h2010 | h2010
                            · linarith only [h1, h2010, hlam]
                            · rcases p2005_3 (m.d 0 4) (by simp) with h2012 | h2012
                              · linarith only [h2, h2012, hlam]
                              · rcases p2005_3 (m.d 0 5) (by simp) with h2014 | h2014
                                · linarith only [h2014, h3, hlam]
                                · rcases h0emin with h2016 | h2016 | h2016 | h2016 | h2016
                                  · rcases h2bigk with h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h0, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h4, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h1990, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h1997, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h1999, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h5, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h1991, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h2001, hlam, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h6, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h1992, hlam, p2017_0]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2005_1, p2017_1]
                                    · have p2017_0 := h2017c.1
                                      have p2017_1 := h2017c.2.1
                                      have p2017_2 := h2017c.2.2.1
                                      have p2017_3 := h2017c.2.2.2
                                      linarith only [hlam, p2017_0]
                                  · linarith only [h2016, hc01, hlam, p2005_1]
                                  · linarith only [h2016, h7, hlam, ht01, ht12, ht23, u3elo3]
                                  · linarith only [h2016, h5, hc01, hlam, p2005_1]
                                  · linarith only [h2016, h6, hc01, hlam, p2005_1]
                        · linarith only [h0, h2007, hlam]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        rcases p2005_3 (m.d 0 1) (by simp) with h2048 | h2048
                        · rcases p2005_3 (m.d 0 2) (by simp) with h2049 | h2049
                          · linarith only [h0, h2049, hlam]
                          · linarith only [h2049, h4, hlam]
                        · linarith only [h1, h2048, hlam]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        rcases p2005_3 (m.d 0 1) (by simp) with h2053 | h2053
                        · rcases p2005_3 (m.d 0 2) (by simp) with h2054 | h2054
                          · linarith only [h0, h2054, hlam]
                          · linarith only [h2054, h5, hlam]
                        · linarith only [h2, h2053, hlam]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        rcases p2005_3 (m.d 0 1) (by simp) with h2058 | h2058
                        · rcases p2005_3 (m.d 0 2) (by simp) with h2059 | h2059
                          · linarith only [h0, h2059, hlam]
                          · linarith only [h2059, h6, hlam]
                        · linarith only [h2058, h3, hlam]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h0, hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        rcases p2005_3 (m.d 0 1) (by simp) with h2065 | h2065
                        · rcases p2005_3 (m.d 0 2) (by simp) with h2066 | h2066
                          · rcases p2005_3 (m.d 0 3) (by simp) with h2067 | h2067
                            · linarith only [h2067, h4, hlam]
                            · rcases p2005_3 (m.d 0 4) (by simp) with h2069 | h2069
                              · linarith only [h2069, h5, hlam]
                              · linarith only [h2069, h7, hlam]
                          · linarith only [h2066, h4, hlam]
                        · linarith only [h1, h2065, hlam]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        rcases p2005_3 (m.d 0 1) (by simp) with h2074 | h2074
                        · rcases p2005_3 (m.d 0 2) (by simp) with h2075 | h2075
                          · rcases p2005_3 (m.d 0 3) (by simp) with h2076 | h2076
                            · linarith only [h2076, h4, hlam]
                            · rcases p2005_3 (m.d 0 4) (by simp) with h2078 | h2078
                              · linarith only [h2078, h5, hlam]
                              · rcases p2005_3 (m.d 0 5) (by simp) with h2080 | h2080
                                · linarith only [h2080, h6, hlam]
                                · linarith only [h1796, h2080, hlam]
                          · linarith only [h2075, h5, hlam]
                        · linarith only [h2, h2074, hlam]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        rcases p2005_3 (m.d 0 1) (by simp) with h2085 | h2085
                        · rcases p2005_3 (m.d 0 2) (by simp) with h2086 | h2086
                          · rcases p2005_3 (m.d 0 3) (by simp) with h2087 | h2087
                            · linarith only [h2087, h4, hlam]
                            · rcases p2005_3 (m.d 0 4) (by simp) with h2089 | h2089
                              · linarith only [h2089, h5, hlam]
                              · rcases p2005_3 (m.d 0 5) (by simp) with h2091 | h2091
                                · linarith only [h2091, h6, hlam]
                                · rcases h0emin with h2093 | h2093 | h2093 | h2093 | h2093
                                  · rcases h2bigk with h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      rcases p2094_3 (m.d 0 2) (by simp) with h2096 | h2096
                                      · rcases p2094_3 (m.d 1 2) (by simp) with h2097 | h2097
                                        · linarith only [h0, h2097, hlam]
                                        · rcases p2094_3 (m.d 2 3) (by simp) with h2099 | h2099
                                          · linarith only [h2099, h4, hlam]
                                          · rcases p2094_3 (m.d 2 4) (by simp) with h2101 | h2101
                                            · linarith only [h2101, h5, hlam]
                                            · rcases p2094_3 (m.d 2 5) (by simp) with h2103 | h2103
                                              · linarith only [h2103, h6, hlam]
                                              · rcases h2emin with h2105 | h2105 | h2105 | h2105 | h2105
                                                · rcases h3bigk with h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2106_1, u3elo0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2106_1, u3elo0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h7, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1616, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2106_1, u3elo1]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1993, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1995, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h4, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1990, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1997, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1999, hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h2003, hc03, hlam, hphi, p2106_1, u3elo4]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1990, h2003, hc23, hlam, hphi, p2106_1, u3elo4]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h2003, hc23, hlam, hphi, p2106_1, u3elo4]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [hlam, p2106_0]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h2003, hlam, p2106_1]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1, h1990, hc23, hlam, hphi, p2106_1, u3elo4]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2106_1, u3elo4]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2106_1, u3elo4]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [h1, h1990, h7, hc23, hlam, hphi, p2106_1, u3elo4]
                                                  · have p2106_0 := h2106c.1
                                                    have p2106_1 := h2106c.2.1
                                                    have p2106_2 := h2106c.2.2.1
                                                    have p2106_3 := h2106c.2.2.2
                                                    linarith only [hlam, p2106_0]
                                                · linarith only [h0, h2105, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2094_1]
                                                · linarith only [h1, h1990, h2105, hlam, ht23, u3elo0]
                                                · linarith only [h0, h1796, h2105, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2005_1]
                                                · linarith only [h0, h2105, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2005_1]
                                      · linarith only [h0, h2096, hlam]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      rcases p2094_3 (m.d 0 2) (by simp) with h2137 | h2137
                                      · rcases p2094_3 (m.d 1 2) (by simp) with h2138 | h2138
                                        · linarith only [h0, h2138, hlam]
                                        · linarith only [h1990, h2138, hlam]
                                      · linarith only [h2137, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      rcases p2094_3 (m.d 0 2) (by simp) with h2142 | h2142
                                      · rcases p2094_3 (m.d 1 2) (by simp) with h2143 | h2143
                                        · linarith only [h0, h2143, hlam]
                                        · linarith only [h1991, h2143, hlam]
                                      · linarith only [h2142, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      rcases p2094_3 (m.d 0 2) (by simp) with h2147 | h2147
                                      · rcases p2094_3 (m.d 1 2) (by simp) with h2148 | h2148
                                        · linarith only [h0, h2148, hlam]
                                        · linarith only [h1992, h2148, hlam]
                                      · linarith only [h2147, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h0, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      rcases p2094_3 (m.d 0 2) (by simp) with h2154 | h2154
                                      · rcases p2094_3 (m.d 1 2) (by simp) with h2155 | h2155
                                        · rcases p2094_3 (m.d 2 3) (by simp) with h2156 | h2156
                                          · linarith only [h2156, hlam, p2094_0]
                                          · rcases p2094_3 (m.d 2 4) (by simp) with h2158 | h2158
                                            · linarith only [h1991, h2158, hlam]
                                            · linarith only [h1997, h2158, hlam]
                                        · linarith only [h2155, hlam, p2094_0]
                                      · linarith only [h2154, h4, hlam]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      rcases p2094_3 (m.d 0 2) (by simp) with h2163 | h2163
                                      · rcases p2094_3 (m.d 1 2) (by simp) with h2164 | h2164
                                        · rcases p2094_3 (m.d 2 3) (by simp) with h2165 | h2165
                                          · linarith only [h1990, h2165, hlam]
                                          · rcases p2094_3 (m.d 2 4) (by simp) with h2167 | h2167
                                            · linarith only [h2167, hlam, p2094_0]
                                            · rcases p2094_3 (m.d 2 5) (by simp) with h2169 | h2169
                                              · linarith only [h1992, h2169, hlam]
                                              · linarith only [h2001, h2169, hlam]
                                        · linarith only [h2164, hlam, p2094_0]
                                      · linarith only [h2163, h5, hlam]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      rcases p2094_3 (m.d 0 2) (by simp) with h2174 | h2174
                                      · rcases p2094_3 (m.d 1 2) (by simp) with h2175 | h2175
                                        · rcases p2094_3 (m.d 2 3) (by simp) with h2176 | h2176
                                          · linarith only [h1990, h2176, hlam]
                                          · rcases p2094_3 (m.d 2 4) (by simp) with h2178 | h2178
                                            · linarith only [h1991, h2178, hlam]
                                            · rcases p2094_3 (m.d 2 5) (by simp) with h2180 | h2180
                                              · linarith only [h2180, hlam, p2094_0]
                                              · rcases h2emin with h2182 | h2182 | h2182 | h2182 | h2182
                                                · rcases h3bigk with h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h2003, h7, hc13, hc45, hlam, hphi, ht34, p2183_1]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h2003, h7, hc23, hc45, hlam, hphi, ht34, p2183_1]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h7, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1616, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2183_1, u3elo1]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1993, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1995, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h4, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1990, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1997, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1999, hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h2003, hc03, hc45, hlam, hphi, ht34, p2183_1]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1990, h2003, hc23, hc45, hlam, hphi, ht34, p2183_1]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h2003, hc23, hc45, hlam, hphi, ht34, p2183_1]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [hlam, p2183_0]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h2003, hlam, p2183_1]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1, h1990, hc23, hlam, hphi, p2183_1, u3elo4]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2183_1, u3elo4]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2183_1, u3elo4]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [h1, h1990, h7, hc23, hlam, hphi, p2183_1, u3elo4]
                                                  · have p2183_0 := h2183c.1
                                                    have p2183_1 := h2183c.2.1
                                                    have p2183_2 := h2183c.2.2.1
                                                    have p2183_3 := h2183c.2.2.2
                                                    linarith only [hlam, p2183_0]
                                                · rcases h3bigk with h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2209_1, u3elo0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2209_1, u3elo0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h7, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1616, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2209_1, u3elo1]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1993, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1995, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h4, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1990, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1997, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1999, hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hc03, hlam, hphi, p2209_1, u3elo3]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2209_1, u3elo3]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2209_1, u3elo3]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hlam, p2209_0]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h2003, hlam, p2209_1]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1, h1990, hc23, hlam, hphi, p2209_1, u3elo4]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2209_1, u3elo4]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2209_1, u3elo4]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [h1, h1990, h7, hc23, hlam, hphi, p2209_1, u3elo4]
                                                  · have p2209_0 := h2209c.1
                                                    have p2209_1 := h2209c.2.1
                                                    have p2209_2 := h2209c.2.2.1
                                                    have p2209_3 := h2209c.2.2.2
                                                    linarith only [hlam, p2209_0]
                                                · linarith only [h1, h1990, h2182, hlam, ht23, u3elo0]
                                                · linarith only [h0, h2001, h2182, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2094_1]
                                                · linarith only [h0, h2182, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2094_1]
                                        · linarith only [h2175, hlam, p2094_0]
                                      · linarith only [h2174, h6, hlam]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h4, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h1990, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h1997, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h1999, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h5, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h1991, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h0, h1796, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2005_1, p2094_1]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h2001, hlam, p2094_1]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h6, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h1992, hlam, p2094_0]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2005_1, p2094_1]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [h0, h1992, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2005_1, p2094_1]
                                    · have p2094_0 := h2094c.1
                                      have p2094_1 := h2094c.2.1
                                      have p2094_2 := h2094c.2.2.1
                                      have p2094_3 := h2094c.2.2.2
                                      linarith only [hlam, p2094_0]
                                  · rcases h2bigk with h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      rcases p2255_3 (m.d 0 2) (by simp) with h2257 | h2257
                                      · rcases p2255_3 (m.d 1 2) (by simp) with h2258 | h2258
                                        · linarith only [h0, h2258, hlam]
                                        · rcases p2255_3 (m.d 2 3) (by simp) with h2260 | h2260
                                          · linarith only [h2260, h4, hlam]
                                          · rcases p2255_3 (m.d 2 4) (by simp) with h2262 | h2262
                                            · linarith only [h2262, h5, hlam]
                                            · rcases p2255_3 (m.d 2 5) (by simp) with h2264 | h2264
                                              · linarith only [h2264, h6, hlam]
                                              · rcases h2emin with h2266 | h2266 | h2266 | h2266 | h2266
                                                · rcases h3bigk with h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h2003, h7, hc13, hc45, hlam, hphi, ht34, p2267_1]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h2003, h7, hc23, hc45, hlam, hphi, ht34, p2267_1]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h7, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1616, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2267_1, u3elo1]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1993, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1995, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h4, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1990, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1997, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1999, hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h2003, hc03, hc45, hlam, hphi, ht34, p2267_1]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1990, h2003, hc23, hc45, hlam, hphi, ht34, p2267_1]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h2003, hc23, hc45, hlam, hphi, ht34, p2267_1]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [hlam, p2267_0]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h2003, hlam, p2267_1]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1, h1990, hc23, hlam, hphi, p2267_1, u3elo4]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2267_1, u3elo4]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2267_1, u3elo4]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [h1, h1990, h7, hc23, hlam, hphi, p2267_1, u3elo4]
                                                  · have p2267_0 := h2267c.1
                                                    have p2267_1 := h2267c.2.1
                                                    have p2267_2 := h2267c.2.2.1
                                                    have p2267_3 := h2267c.2.2.2
                                                    linarith only [hlam, p2267_0]
                                                · linarith only [h0, h2266, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2255_1]
                                                · linarith only [h1, h1990, h2266, hlam, ht23, u3elo0]
                                                · linarith only [h0, h1796, h2266, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2005_1]
                                                · linarith only [h0, h1992, h2266, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2255_1]
                                      · linarith only [h0, h2257, hlam]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      rcases p2255_3 (m.d 0 2) (by simp) with h2298 | h2298
                                      · rcases p2255_3 (m.d 1 2) (by simp) with h2299 | h2299
                                        · linarith only [h0, h2299, hlam]
                                        · linarith only [h1990, h2299, hlam]
                                      · linarith only [h2298, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      rcases p2255_3 (m.d 0 2) (by simp) with h2303 | h2303
                                      · rcases p2255_3 (m.d 1 2) (by simp) with h2304 | h2304
                                        · linarith only [h0, h2304, hlam]
                                        · linarith only [h1991, h2304, hlam]
                                      · linarith only [h2303, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      rcases p2255_3 (m.d 0 2) (by simp) with h2308 | h2308
                                      · rcases p2255_3 (m.d 1 2) (by simp) with h2309 | h2309
                                        · linarith only [h0, h2309, hlam]
                                        · linarith only [h1992, h2309, hlam]
                                      · linarith only [h2308, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h0, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      rcases p2255_3 (m.d 0 2) (by simp) with h2315 | h2315
                                      · rcases p2255_3 (m.d 1 2) (by simp) with h2316 | h2316
                                        · rcases p2255_3 (m.d 2 3) (by simp) with h2317 | h2317
                                          · linarith only [h2317, hlam, p2255_0]
                                          · rcases p2255_3 (m.d 2 4) (by simp) with h2319 | h2319
                                            · linarith only [h1991, h2319, hlam]
                                            · linarith only [h1997, h2319, hlam]
                                        · linarith only [h2316, hlam, p2255_0]
                                      · linarith only [h2315, h4, hlam]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      rcases p2255_3 (m.d 0 2) (by simp) with h2324 | h2324
                                      · rcases p2255_3 (m.d 1 2) (by simp) with h2325 | h2325
                                        · rcases p2255_3 (m.d 2 3) (by simp) with h2326 | h2326
                                          · linarith only [h1990, h2326, hlam]
                                          · rcases p2255_3 (m.d 2 4) (by simp) with h2328 | h2328
                                            · linarith only [h2328, hlam, p2255_0]
                                            · rcases p2255_3 (m.d 2 5) (by simp) with h2330 | h2330
                                              · linarith only [h1992, h2330, hlam]
                                              · linarith only [h2001, h2330, hlam]
                                        · linarith only [h2325, hlam, p2255_0]
                                      · linarith only [h2324, h5, hlam]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      rcases p2255_3 (m.d 0 2) (by simp) with h2335 | h2335
                                      · rcases p2255_3 (m.d 1 2) (by simp) with h2336 | h2336
                                        · rcases p2255_3 (m.d 2 3) (by simp) with h2337 | h2337
                                          · linarith only [h1990, h2337, hlam]
                                          · rcases p2255_3 (m.d 2 4) (by simp) with h2339 | h2339
                                            · linarith only [h1991, h2339, hlam]
                                            · rcases p2255_3 (m.d 2 5) (by simp) with h2341 | h2341
                                              · linarith only [h2341, hlam, p2255_0]
                                              · rcases h2emin with h2343 | h2343 | h2343 | h2343 | h2343
                                                · rcases h3bigk with h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c | h2344c
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h2003, h7, hc13, hc45, hlam, hphi, ht34, p2344_1]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h2003, h7, hc23, hc45, hlam, hphi, ht34, p2344_1]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h7, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1616, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2344_1, u3elo1]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1993, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1995, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h4, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1990, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1997, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1999, hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h2003, hc03, hc45, hlam, hphi, ht34, p2344_1]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h2003, hc13, hc45, hlam, hphi, ht34, p2344_1]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h2003, hc23, hc45, hlam, hphi, ht34, p2344_1]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [hlam, p2344_0]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h2003, hlam, p2344_1]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [hc03, hlam, hphi, p2344_1, u3elo4]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2344_1, u3elo4]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2344_1, u3elo4]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [h1, h1990, h7, hc23, hlam, hphi, p2344_1, u3elo4]
                                                  · have p2344_0 := h2344c.1
                                                    have p2344_1 := h2344c.2.1
                                                    have p2344_2 := h2344c.2.2.1
                                                    have p2344_3 := h2344c.2.2.2
                                                    linarith only [hlam, p2344_0]
                                                · rcases h3bigk with h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2370_1, u3elo0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2370_1, u3elo0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h7, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1616, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2370_1, u3elo1]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1993, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1995, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h4, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1990, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1997, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1999, hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hc03, hlam, hphi, p2370_1, u3elo3]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2370_1, u3elo3]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2370_1, u3elo3]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hlam, p2370_0]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h2003, hlam, p2370_1]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1, h1990, hc23, hlam, hphi, p2370_1, u3elo4]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1990, hc23, hlam, hphi, p2370_1, u3elo4]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hc23, hlam, hphi, p2370_1, u3elo4]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [h1, h1990, h7, hc23, hlam, hphi, p2370_1, u3elo4]
                                                  · have p2370_0 := h2370c.1
                                                    have p2370_1 := h2370c.2.1
                                                    have p2370_2 := h2370c.2.2.1
                                                    have p2370_3 := h2370c.2.2.2
                                                    linarith only [hlam, p2370_0]
                                                · linarith only [h1, h1990, h2343, hlam, ht23, u3elo0]
                                                · linarith only [h0, h2001, h2343, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2255_1]
                                                · linarith only [h0, h2343, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2255_1]
                                        · linarith only [h2336, hlam, p2255_0]
                                      · linarith only [h2335, h6, hlam]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h4, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h1990, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h1997, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h1999, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h5, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h1991, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h0, h1796, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2005_1, p2255_1]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h2001, hlam, p2255_1]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h6, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h1992, hlam, p2255_0]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2005_1, p2255_1]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [h0, h1992, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2005_1, p2255_1]
                                    · have p2255_0 := h2255c.1
                                      have p2255_1 := h2255c.2.1
                                      have p2255_2 := h2255c.2.2.1
                                      have p2255_3 := h2255c.2.2.2
                                      linarith only [hlam, p2255_0]
                                  · linarith only [h2093, h7, hlam, ht01, ht12, ht23, u3elo3]
                                  · linarith only [h0, h1796, h2093, hc01, hlam, p2005_1]
                                  · linarith only [h0, h2093, hc01, hlam, p2005_1]
                          · linarith only [h2086, h6, hlam]
                        · linarith only [h2085, h3, hlam]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h1, hlam, p2005_1]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h4, hlam, p2005_1]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h7, hlam, p2005_1]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h1616, hlam, p2005_1]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h2, hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h5, hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h1, h7, hc13, hlam, hphi, p2005_1, u3elo3]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h1796, hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h3, hlam, p2005_0]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h6, hlam, p2005_1]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h1, h1616, hc13, hlam, hphi, p2005_1, u3elo4]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [h1, h1616, h7, hc13, hlam, hphi, p2005_1, u3elo4]
                      · have p2005_0 := h2005c.1
                        have p2005_1 := h2005c.2.1
                        have p2005_2 := h2005c.2.2.1
                        have p2005_3 := h2005c.2.2.2
                        linarith only [hlam, p2005_0]
        · linarith only [h1616, h1990, h1992, h6, hc23, hlam, hphi, u3elo4]
      · linarith only [h1990, h1991, h5, h7, hc23, hlam, hphi, u3elo3]
    · linarith only [h1990, h4, h7, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h1616 | h1616
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h1616
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h1616

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h2439 | h2439
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2440 | h2440
    · linarith only [h2440, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2442 | h2442
      · linarith only [h2442, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2444 | h2444
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2445 | h2445
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2446 | h2446
            · linarith only [h0, h2446, h6, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2448 | h2448
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2449 | h2449
                · linarith only [h1, h2440, h2449, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2451 | h2451
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2452 | h2452
                    · linarith only [h0, h2440, h2444, h2452, h6, hlam]
                    · linarith only [h0, h2444, h2452, h6, hc23, hlam, hphi, u3elo4]
                  · linarith only [h2439, h2440, h2451, hc23, hlam, hphi, u3elo4]
              · linarith only [h2439, h2440, h2448, hc13, hlam, hphi, u3elo4]
          · linarith only [h2444, h2445, h5, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · linarith only [h2440, h2444, h4, h6, hc12, hlam, hphi, ht23, u3elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2459 | h2459
    · linarith only [h2439, h2459, h4, h6, hc23, hlam, hphi, u3elo3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2461 | h2461
      · linarith only [h2461, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2463 | h2463
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2464 | h2464
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2465 | h2465
            · linarith only [h0, h2465, h6, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2467 | h2467
              · linarith only [h2439, h2467, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2469 | h2469
                · linarith only [h0, h1, h2439, h2459, h2463, h2469, h6, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2471 | h2471
                  · linarith only [h0, h1, h2439, h2463, h2471, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2473 | h2473
                    · linarith only [h2459, h2473, h4, h6, hlam]
                    · linarith only [h0, h2464, h2471, h2473, h6, hc23, hlam, hphi, u3elo4]
          · linarith only [h2463, h2464, h5, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · linarith only [h2459, h2463, h4, h6, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h2478 | h2478
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2479 | h2479
    · linarith only [h2479, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2481 | h2481
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2482 | h2482
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2483 | h2483
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2484 | h2484
            · linarith only [h0, h2484, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2486 | h2486
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2487 | h2487
                · linarith only [h2479, h2487, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2489 | h2489
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2490 | h2490
                    · linarith only [h0, h1, h2479, h2483, h2489, h2490, hc02, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2490, h4, h5, hc23, hlam, hphi, u3elo3]
                  · linarith only [h2479, h2481, h2489, hc13, hlam, hphi, u3elo3]
              · linarith only [h2478, h2483, h2486, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h2479, h2483, h4, h5, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h2479, h2481, h2482, h4, h5, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2497 | h2497
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2498 | h2498
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2499 | h2499
            · linarith only [h0, h2499, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2501 | h2501
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2502 | h2502
                · linarith only [h1, h2479, h2502, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2504 | h2504
                  · linarith only [h1, h2481, h2504, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2506 | h2506
                    · linarith only [h0, h2479, h2498, h2506, h5, hlam]
                    · linarith only [h0, h2498, h2506, h5, hc23, hlam, hphi, u3elo3]
              · linarith only [h2478, h2498, h2501, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h2479, h2498, h4, h5, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h2478, h2497, h5, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2512 | h2512
    · linarith only [h2512, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2514 | h2514
      · linarith only [h2478, h2514, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2516 | h2516
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2517 | h2517
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2518 | h2518
            · linarith only [h0, h2518, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2520 | h2520
              · linarith only [h0, h2478, h2520, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2522 | h2522
                · linarith only [h2512, h2522, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2524 | h2524
                  · linarith only [h0, h1, h2478, h2514, h2517, h2524, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2526 | h2526
                    · linarith only [h0, h1, h2512, h2517, h2526, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h2526, h4, h5, hc23, hlam, hphi, u3elo3]
          · linarith only [h2517, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2530 | h2530
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2531 | h2531
            · linarith only [h0, h2531, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2533 | h2533
              · linarith only [h0, h2478, h2533, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2535 | h2535
                · linarith only [h1, h2512, h2535, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2537 | h2537
                  · linarith only [h0, h1, h2512, h2514, h2516, h2530, h2537, h5, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2539 | h2539
                    · linarith only [h0, h1, h2512, h2530, h2539, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h2539, h4, h5, hc23, hlam, hphi, u3elo3]
          · linarith only [h2530, h4, h5, hc12, hc24, hlam, hphi]

end R2N4
