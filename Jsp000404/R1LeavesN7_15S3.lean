import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h1820 | h1820
  · linarith only [h1820, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1822 | h1822
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1823 | h1823
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1824 | h1824
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1825 | h1825
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1826 | h1826
            · linarith only [h1, h1826, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1828 | h1828
              · linarith only [h1820, h1828, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1830 | h1830
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1831 | h1831
                  · linarith only [h1, h1822, h1831, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1833 | h1833
                    · linarith only [h1820, h1823, h1833, h2, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1835 | h1835
                      · linarith only [h1820, h1824, h1830, h1831, h1835, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c | h1837c
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h0, h1824, h1831, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          rcases p1837_3 (m.d 0 1) (by simp) with h1841 | h1841
                          · rcases p1837_3 (m.d 0 2) (by simp) with h1842 | h1842
                            · linarith only [h0, h1842, hlam]
                            · linarith only [h1842, h5, hlam]
                          · linarith only [h1841, h2, hlam]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h1822, h1826, h1830, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h0, hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h1, h1822, h1830, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          rcases p1837_3 (m.d 0 1) (by simp) with h1850 | h1850
                          · rcases p1837_3 (m.d 0 2) (by simp) with h1851 | h1851
                            · rcases p1837_3 (m.d 0 3) (by simp) with h1852 | h1852
                              · linarith only [h1852, h4, hlam]
                              · linarith only [h1852, h7, hlam]
                            · linarith only [h1851, h5, hlam]
                          · linarith only [h1850, h2, hlam]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h0, h1822, h1826, h1830, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h1, hlam, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h4, hlam, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h1823, h1830, h1835, h2, h8, hc34, hc45, hlam, hphi, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h8, hlam, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h2, hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h5, hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h7, hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h1820, hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h3, hlam, p1837_0]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h6, hlam, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h1, h1822, h1830, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [h1823, h1830, h1835, h2, h8, hc34, hc45, hlam, hphi, p1837_1]
                        · have p1837_0 := h1837c.1
                          have p1837_1 := h1837c.2.1
                          have p1837_2 := h1837c.2.2.1
                          have p1837_3 := h1837c.2.2.2
                          linarith only [hlam, p1837_0]
                · linarith only [h1830, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1822, h1825, h7, h8, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1875 | h1875
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1876 | h1876
            · linarith only [h1, h1876, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1878 | h1878
              · linarith only [h1820, h1878, h2, h7, h8, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1880 | h1880
                · linarith only [h0, h1822, h1824, h1880, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1880, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1875, h7, h8, hc13, hc35, hlam, hphi]
      · linarith only [h1820, h1822, h1823, h5, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1885 | h1885
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1886 | h1886
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1887 | h1887
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1888 | h1888
            · linarith only [h1822, h1885, h1888, h4, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1822, h1886, h1888, hlam]
          · linarith only [h1822, h1885, h1887, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1892 | h1892
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1893 | h1893
            · linarith only [h1, h1893, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1895 | h1895
              · linarith only [h1820, h1822, h1885, h1895, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1897 | h1897
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1898 | h1898
                  · linarith only [h1898, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1900 | h1900
                    · linarith only [h1820, h1885, h1900, h2, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1902 | h1902
                      · linarith only [h0, h1820, h1822, h1885, h1897, h1898, h1902, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h1822, h1885, h1897, h1902, h4, h8, hc34, hc45, hlam, hphi]
                · linarith only [h1822, h1885, h1897, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h1822, h1885, h1892, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1907 | h1907
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1908 | h1908
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1909 | h1909
            · linarith only [h1, h1909, h8, hlam]
            · linarith only [h1820, h1885, h1907, h1908, h1909, h5, hc34, hc45, hlam, hphi]
          · linarith only [h1908, h7, h8, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1913 | h1913
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1914 | h1914
            · linarith only [h1, h1914, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1916 | h1916
              · linarith only [h1820, h1822, h1885, h1913, h1916, h5, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1918 | h1918
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1919 | h1919
                  · linarith only [h1919, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1921 | h1921
                    · linarith only [h1820, h1921, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1923 | h1923
                      · linarith only [h1820, h1822, h1885, h1913, h1923, h4, h5, h8, hc12, hc35, hlam, hphi, ht23]
                      · rcases h0bigk with h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1822, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1, h1913, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1885, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1, h1913, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h0, hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1, h1913, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h0, h1885, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h0, h1822, h1913, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1, hlam, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h4, hlam, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1885, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h8, hlam, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h2, hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h5, hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h7, hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1820, hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h3, hlam, p1925_0]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h6, hlam, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1, h1913, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [h1885, h1923, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1925_1]
                        · have p1925_0 := h1925c.1
                          have p1925_1 := h1925c.2.1
                          have p1925_2 := h1925c.2.2.1
                          have p1925_3 := h1925c.2.2.2
                          linarith only [hlam, p1925_0]
                · linarith only [h1, h1822, h1913, h1918, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1913, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8

set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1953 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h1954 | h1954
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1955 | h1955
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1956 | h1956
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1957 | h1957
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1958 | h1958
          · linarith only [h1, h1953, h1958, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1960 | h1960
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1961 | h1961
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1962 | h1962
                · linarith only [h0, h1, h1960, h1962, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1964 | h1964
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1965 | h1965
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1966 | h1966
                      · rcases h0bigk with h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h0, h1956, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h1, h1955, h1964, h1966, hc01, hc45, hlam, hphi, ht0b, ht5b, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h1, h1955, h1964, h1966, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          rcases p1967_3 (m.d 0 1) (by simp) with h1972 | h1972
                          · rcases p1967_3 (m.d 0 2) (by simp) with h1973 | h1973
                            · linarith only [h0, h1973, hlam]
                            · linarith only [h1973, h6, hlam]
                          · linarith only [h1972, h3, hlam]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h0, hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h1, h1955, h1964, h1966, hc02, hc45, hlam, hphi, ht0b, ht5b, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h0, h1, h1955, h1964, h1966, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          rcases p1967_3 (m.d 0 1) (by simp) with h1981 | h1981
                          · rcases p1967_3 (m.d 0 2) (by simp) with h1982 | h1982
                            · rcases p1967_3 (m.d 0 3) (by simp) with h1983 | h1983
                              · linarith only [h1983, h4, hlam]
                              · linarith only [h1953, h1983, hlam]
                            · linarith only [h1982, h6, hlam]
                          · linarith only [h1981, h3, hlam]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h1, hlam, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h4, hlam, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h7, hlam, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h2, hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h5, hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h1, h1955, h1964, h1966, hc04, hc45, hlam, hphi, ht0b, ht5b, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          rcases p1967_3 (m.d 0 1) (by simp) with h1997 | h1997
                          · rcases p1967_3 (m.d 0 2) (by simp) with h1998 | h1998
                            · rcases p1967_3 (m.d 0 3) (by simp) with h1999 | h1999
                              · linarith only [h1999, h7, hlam]
                              · linarith only [h1953, h1999, hlam]
                            · linarith only [h1998, h6, hlam]
                          · linarith only [h1997, h3, hlam]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h3, hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h6, hlam, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h1953, hlam, p1967_0]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [h1954, hlam, p1967_1]
                        · have p1967_0 := h1967c.1
                          have p1967_1 := h1967c.2.1
                          have p1967_2 := h1967c.2.2.1
                          have p1967_3 := h1967c.2.2.2
                          linarith only [hlam, p1967_0]
                      · linarith only [h1, h1954, h1955, h1964, h1966, h7, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h1956, h1961, h1962, h1964, h1965, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1953, h1964, h7, hc23, hc34, hlam, hphi]
              · linarith only [h1958, h1960, h1961, hlam]
            · linarith only [h1953, h1960, h7, hc13, hc34, hlam, hphi]
        · linarith only [h1953, h1955, h1957, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2015 | h2015
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2016 | h2016
          · linarith only [h1, h1953, h2016, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2018 | h2018
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2019 | h2019
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2020 | h2020
                · linarith only [h1955, h1956, h2020, h5, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2022 | h2022
                  · linarith only [h0, h1955, h1956, h2022, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h2018, h2022, h7, hc23, hc34, hlam, hphi]
              · linarith only [h1953, h1954, h1955, h1956, h2019, h7, hc23, hc34, hlam, hphi]
            · linarith only [h1953, h2018, h7, hc13, hc34, hlam, hphi]
        · linarith only [h1953, h1955, h2015, h6, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2028 | h2028
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2029 | h2029
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2030 | h2030
          · linarith only [h1953, h1955, h2030, h4, h7, hc02, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h1955, h2028, h2030, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2033 | h2033
          · linarith only [h1953, h2028, h2029, h2033, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h1955, h2028, h2033, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2036 | h2036
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2037 | h2037
          · linarith only [h1955, h2036, h2037, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2039 | h2039
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2040 | h2040
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2041 | h2041
                · linarith only [h2041, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2043 | h2043
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2044 | h2044
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2045 | h2045
                      · rcases h0bigk with h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1955, h2036, h2041, h2043, h2045, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1955, h2036, h2043, h2045, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1955, h2036, h2043, h2045, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          rcases p2046_3 (m.d 0 1) (by simp) with h2051 | h2051
                          · rcases p2046_3 (m.d 0 2) (by simp) with h2052 | h2052
                            · linarith only [h0, h2052, hlam]
                            · linarith only [h2052, h6, hlam]
                          · linarith only [h2051, h3, hlam]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h0, hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1955, h2036, h2043, h2045, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h0, h1955, h2036, h2043, h2045, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          rcases p2046_3 (m.d 0 1) (by simp) with h2060 | h2060
                          · rcases p2046_3 (m.d 0 2) (by simp) with h2061 | h2061
                            · rcases p2046_3 (m.d 0 3) (by simp) with h2062 | h2062
                              · linarith only [h2062, h4, hlam]
                              · linarith only [h1953, h2062, hlam]
                            · linarith only [h2061, h6, hlam]
                          · linarith only [h2060, h3, hlam]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h4, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h7, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2036, h2043, h2045, h3, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2, hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h5, hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1955, h2, h2036, h2043, h2045, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          rcases p2046_3 (m.d 0 1) (by simp) with h2076 | h2076
                          · rcases p2046_3 (m.d 0 2) (by simp) with h2077 | h2077
                            · rcases p2046_3 (m.d 0 3) (by simp) with h2078 | h2078
                              · linarith only [h2078, h7, hlam]
                              · linarith only [h1953, h2078, hlam]
                            · linarith only [h2077, h6, hlam]
                          · linarith only [h2076, h3, hlam]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h3, hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h6, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1953, hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1954, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                      · linarith only [h1955, h2045, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1955, h2036, h2040, h2041, h2043, h2044, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1953, h1955, h2036, h2043, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h1955, h2036, h2037, h2040, hlam]
            · linarith only [h1953, h1955, h2039, h7, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2093 | h2093
          · linarith only [h1, h1953, h2093, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2095 | h2095
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2096 | h2096
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2097 | h2097
                · linarith only [h2097, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2099 | h2099
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2100 | h2100
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2101 | h2101
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
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h1953, h2036, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h2, h2093, h2095, h2101, hc01, hc45, hlam, hphi, ht0b, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h2036, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h0, hlam, p2102_0]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [hlam, p2102_0]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h1953, h2036, h6, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h0, h2, h2093, h2095, h2101, hc01, hc45, hlam, hphi, ht0b, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h0, h2036, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h1, hlam, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h4, hlam, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [hlam, p2102_0]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h7, hlam, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h2036, h6, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h2, hlam, p2102_0]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h5, hlam, p2102_0]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h1, h2095, h2101, hc04, hc45, hlam, hphi, ht0b, ht5b, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [hlam, p2102_0]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h2036, h6, h7, hc12, hc34, hlam, hphi, ht23, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h3, hlam, p2102_0]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h6, hlam, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h1953, hlam, p2102_0]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [h1954, hlam, p2102_1]
                        · have p2102_0 := h2102c.1
                          have p2102_1 := h2102c.2.1
                          have p2102_2 := h2102c.2.2.1
                          have p2102_3 := h2102c.2.2.2
                          linarith only [hlam, p2102_0]
                      · linarith only [h2036, h2099, h2101, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h2, h2028, h2096, h2100, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1, h2095, h2099, h7, hc23, hc34, hlam, hphi]
              · linarith only [h2093, h2095, h2096, hlam]
            · linarith only [h1953, h2095, h7, hc13, hc34, hlam, hphi]
  · linarith only [h1953, h1954, h7, hlam]

set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1953 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h2134 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h2135 | h2135
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2136 | h2136
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2137 | h2137
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2138 | h2138
        · linarith only [h1, h2138, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2140 | h2140
          · linarith only [h1, h1953, h2140, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2142 | h2142
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2143 | h2143
              · linarith only [h2143, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2145 | h2145
                · linarith only [h1, h1953, h2135, h2145, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2147 | h2147
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2148 | h2148
                    · rcases h0bigk with h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [hlam, p2149_0]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h0, h2136, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        rcases p2149_3 (m.d 0 1) (by simp) with h2152 | h2152
                        · rcases p2149_3 (m.d 0 2) (by simp) with h2153 | h2153
                          · linarith only [h0, h2153, hlam]
                          · linarith only [h2153, h4, hlam]
                        · linarith only [h1, h2152, hlam]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h2, h2136, h2147, hc01, hc45, hlam, hphi, ht0b, ht5b, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        rcases p2149_3 (m.d 0 1) (by simp) with h2158 | h2158
                        · rcases p2149_3 (m.d 0 2) (by simp) with h2159 | h2159
                          · linarith only [h0, h2159, hlam]
                          · linarith only [h2159, h6, hlam]
                        · linarith only [h2158, h3, hlam]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h0, hlam, p2149_0]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [hlam, p2149_0]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        rcases p2149_3 (m.d 0 1) (by simp) with h2165 | h2165
                        · rcases p2149_3 (m.d 0 2) (by simp) with h2166 | h2166
                          · rcases p2149_3 (m.d 0 3) (by simp) with h2167 | h2167
                            · linarith only [h2167, h4, hlam]
                            · rcases p2149_3 (m.d 0 4) (by simp) with h2169 | h2169
                              · linarith only [h2169, h5, hlam]
                              · linarith only [h2169, h7, hlam]
                          · linarith only [h2166, h4, hlam]
                        · linarith only [h1, h2165, hlam]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h2, h2136, h2147, hc02, hc45, hlam, hphi, ht0b, ht5b, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        rcases p2149_3 (m.d 0 1) (by simp) with h2175 | h2175
                        · rcases p2149_3 (m.d 0 2) (by simp) with h2176 | h2176
                          · rcases p2149_3 (m.d 0 3) (by simp) with h2177 | h2177
                            · linarith only [h2177, h4, hlam]
                            · rcases p2149_3 (m.d 0 4) (by simp) with h2179 | h2179
                              · linarith only [h2179, h5, hlam]
                              · linarith only [h2134, h2179, hlam]
                          · linarith only [h2176, h6, hlam]
                        · linarith only [h2175, h3, hlam]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h1, hlam, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h4, hlam, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [hlam, p2149_0]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h7, hlam, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h1953, hlam, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h2, hlam, p2149_0]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h5, hlam, p2149_0]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h1, h2135, h7, hc23, hc34, hlam, hphi, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [hlam, p2149_0]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h1, h1953, h2135, h7, hc23, hc34, hlam, hphi, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h3, hlam, p2149_0]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h6, hlam, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h1, h1953, h2135, hc23, hc35, hlam, hphi, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [h2134, hlam, p2149_1]
                      · have p2149_0 := h2149c.1
                        have p2149_1 := h2149c.2.1
                        have p2149_2 := h2149c.2.2.1
                        have p2149_3 := h2149c.2.2.2
                        linarith only [hlam, p2149_0]
                    · linarith only [h0, h2136, h2147, h2148, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2200 | h2200
                    · rcases h0bigk with h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [hlam, p2201_0]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        rcases p2201_3 (m.d 0 1) (by simp) with h2204 | h2204
                        · rcases p2201_3 (m.d 0 2) (by simp) with h2205 | h2205
                          · linarith only [h0, h2205, hlam]
                          · linarith only [h2205, h4, hlam]
                        · linarith only [h1, h2204, hlam]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h2, h2142, h2143, h2147, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h2142, h2143, h2147, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h0, hlam, p2201_0]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [hlam, p2201_0]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        rcases p2201_3 (m.d 0 1) (by simp) with h2213 | h2213
                        · rcases p2201_3 (m.d 0 2) (by simp) with h2214 | h2214
                          · rcases p2201_3 (m.d 0 3) (by simp) with h2215 | h2215
                            · linarith only [h2215, h4, hlam]
                            · rcases p2201_3 (m.d 0 4) (by simp) with h2217 | h2217
                              · linarith only [h2217, h5, hlam]
                              · linarith only [h2217, h7, hlam]
                          · linarith only [h2214, h4, hlam]
                        · linarith only [h1, h2213, hlam]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h2, h2142, h2143, h2147, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h0, h2142, h2143, h2147, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h1, hlam, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h4, hlam, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [hlam, p2201_0]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h7, hlam, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h1953, hlam, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h2, hlam, p2201_0]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h5, hlam, p2201_0]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h1, h2135, h7, hc23, hc34, hlam, hphi, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [hlam, p2201_0]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h2142, h2143, h2147, h3, h7, hc23, hc34, hlam, hphi, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h3, hlam, p2201_0]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h6, hlam, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h1, h1953, h2135, h2200, hc23, hc34, hlam, hphi, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [h2134, hlam, p2201_1]
                      · have p2201_0 := h2201c.1
                        have p2201_1 := h2201c.2.1
                        have p2201_2 := h2201c.2.2.1
                        have p2201_3 := h2201c.2.2.2
                        linarith only [hlam, p2201_0]
                    · linarith only [h2, h2142, h2200, h7, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2240 | h2240
              · linarith only [h2134, h2135, h2138, h2142, h2240, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2242 | h2242
                · linarith only [h1, h1953, h2135, h2242, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2244 | h2244
                  · linarith only [h0, h2136, h2138, h2142, h2244, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2246 | h2246
                    · rcases h0bigk with h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c | h2247c
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        rcases p2247_3 (m.d 0 1) (by simp) with h2250 | h2250
                        · rcases p2247_3 (m.d 0 2) (by simp) with h2251 | h2251
                          · linarith only [h0, h2251, hlam]
                          · linarith only [h2251, h4, hlam]
                        · linarith only [h1, h2250, hlam]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2134, h2135, h2138, h2142, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2134, h2135, h2138, h2142, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h0, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        rcases p2247_3 (m.d 0 1) (by simp) with h2259 | h2259
                        · rcases p2247_3 (m.d 0 2) (by simp) with h2260 | h2260
                          · rcases p2247_3 (m.d 0 3) (by simp) with h2261 | h2261
                            · linarith only [h2261, h4, hlam]
                            · rcases p2247_3 (m.d 0 4) (by simp) with h2263 | h2263
                              · linarith only [h2263, h5, hlam]
                              · linarith only [h2263, h7, hlam]
                          · linarith only [h2260, h4, hlam]
                        · linarith only [h1, h2259, hlam]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2134, h2135, h2138, h2142, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h0, h2134, h2135, h2138, h2142, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h1, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h4, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h7, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h1953, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h5, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h1, h2135, h7, hc23, hc34, hlam, hphi, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2134, h2135, h2138, h2142, h7, hc23, hc34, hlam, hphi, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h3, hlam, p2247_0]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h6, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h1, h1953, h2135, hc23, hc35, hlam, hphi, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [h2134, hlam, p2247_1]
                      · have p2247_0 := h2247c.1
                        have p2247_1 := h2247c.2.1
                        have p2247_2 := h2247c.2.2.1
                        have p2247_3 := h2247c.2.2.2
                        linarith only [hlam, p2247_0]
                    · linarith only [h2134, h2246, h7, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2286 | h2286
        · linarith only [h1, h2134, h2135, h2137, h2286, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2288 | h2288
          · linarith only [h1, h1953, h2288, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2290 | h2290
            · linarith only [h2136, h2137, h2290, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2292 | h2292
              · linarith only [h1, h2134, h2135, h2290, h2292, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2294 | h2294
                · linarith only [h1, h1953, h2135, h2294, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2296 | h2296
                  · linarith only [h2136, h2137, h2290, h2296, hlam]
                  · linarith only [h2134, h2136, h2137, h2292, h2296, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2299 | h2299
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2300 | h2300
        · linarith only [h1, h1953, h2, h2135, h2136, h2300, h7, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2302 | h2302
          · linarith only [h1, h1953, h2302, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2304 | h2304
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2305 | h2305
              · linarith only [h1953, h2136, h2305, h4, h5, h7, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2307 | h2307
                · linarith only [h0, h1953, h2135, h2136, h2307, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2309 | h2309
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2310 | h2310
                    · rcases h0bigk with h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [hlam, p2311_0]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h2136, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        rcases p2311_3 (m.d 0 1) (by simp) with h2314 | h2314
                        · rcases p2311_3 (m.d 0 2) (by simp) with h2315 | h2315
                          · linarith only [h0, h2315, hlam]
                          · linarith only [h2315, h4, hlam]
                        · linarith only [h1, h2314, hlam]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h2136, h2299, h2307, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        rcases p2311_3 (m.d 0 1) (by simp) with h2320 | h2320
                        · rcases p2311_3 (m.d 0 2) (by simp) with h2321 | h2321
                          · linarith only [h0, h2321, hlam]
                          · linarith only [h2321, h6, hlam]
                        · linarith only [h2320, h3, hlam]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h0, hlam, p2311_0]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [hlam, p2311_0]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        rcases p2311_3 (m.d 0 1) (by simp) with h2327 | h2327
                        · rcases p2311_3 (m.d 0 2) (by simp) with h2328 | h2328
                          · rcases p2311_3 (m.d 0 3) (by simp) with h2329 | h2329
                            · linarith only [h2329, h4, hlam]
                            · rcases p2311_3 (m.d 0 4) (by simp) with h2331 | h2331
                              · linarith only [h2331, h5, hlam]
                              · linarith only [h2331, h7, hlam]
                          · linarith only [h2328, h4, hlam]
                        · linarith only [h1, h2327, hlam]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h2136, h2299, h2307, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        rcases p2311_3 (m.d 0 1) (by simp) with h2337 | h2337
                        · rcases p2311_3 (m.d 0 2) (by simp) with h2338 | h2338
                          · rcases p2311_3 (m.d 0 3) (by simp) with h2339 | h2339
                            · linarith only [h2339, h4, hlam]
                            · rcases p2311_3 (m.d 0 4) (by simp) with h2341 | h2341
                              · linarith only [h2341, h5, hlam]
                              · linarith only [h2134, h2341, hlam]
                          · linarith only [h2338, h6, hlam]
                        · linarith only [h2337, h3, hlam]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h1, hlam, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h4, hlam, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [hlam, p2311_0]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h7, hlam, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h1953, hlam, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h2, hlam, p2311_0]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h5, hlam, p2311_0]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h1, h2135, h7, hc23, hc34, hlam, hphi, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [hlam, p2311_0]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h1, h1953, h2135, h7, hc23, hc34, hlam, hphi, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h3, hlam, p2311_0]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h6, hlam, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h1, h1953, h2135, hc23, hc35, hlam, hphi, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [h2134, hlam, p2311_1]
                      · have p2311_0 := h2311c.1
                        have p2311_1 := h2311c.2.1
                        have p2311_2 := h2311c.2.2.1
                        have p2311_3 := h2311c.2.2.2
                        linarith only [hlam, p2311_0]
                    · linarith only [h2136, h2299, h2307, h2310, h5, h7, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h2136, h2299, h2304, h2307, h2309, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h2134, h2135, h2136, h2304, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2364 | h2364
        · linarith only [h1, h2135, h2136, h2364, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2366 | h2366
          · linarith only [h1, h1953, h2366, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2368 | h2368
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2369 | h2369
              · linarith only [h0, h2135, h2136, h2369, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2371 | h2371
                · linarith only [h1953, h2135, h2299, h2371, h6, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2373 | h2373
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2374 | h2374
                    · rcases h0bigk with h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [hlam, p2375_0]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h2299, h2373, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        rcases p2375_3 (m.d 0 1) (by simp) with h2378 | h2378
                        · rcases p2375_3 (m.d 0 2) (by simp) with h2379 | h2379
                          · linarith only [h0, h2379, hlam]
                          · linarith only [h2379, h4, hlam]
                        · linarith only [h1, h2378, hlam]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h2135, h2299, h2373, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h2135, h2299, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h0, hlam, p2375_0]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [hlam, p2375_0]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        rcases p2375_3 (m.d 0 1) (by simp) with h2387 | h2387
                        · rcases p2375_3 (m.d 0 2) (by simp) with h2388 | h2388
                          · rcases p2375_3 (m.d 0 3) (by simp) with h2389 | h2389
                            · linarith only [h2389, h4, hlam]
                            · rcases p2375_3 (m.d 0 4) (by simp) with h2391 | h2391
                              · linarith only [h2391, h5, hlam]
                              · linarith only [h2391, h7, hlam]
                          · linarith only [h2388, h4, hlam]
                        · linarith only [h1, h2387, hlam]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h2135, h2299, h2373, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h0, h2135, h2299, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h1, hlam, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h4, hlam, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [hlam, p2375_0]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h7, hlam, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h1953, hlam, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h2, hlam, p2375_0]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h5, hlam, p2375_0]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h1, h2135, h7, hc23, hc34, hlam, hphi, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [hlam, p2375_0]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h2135, h2299, h6, h7, hc23, hc34, hlam, hphi, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h3, hlam, p2375_0]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h6, hlam, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h1, h1953, h2135, hc23, hc35, hlam, hphi, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [h2134, hlam, p2375_1]
                      · have p2375_0 := h2375c.1
                        have p2375_1 := h2375c.2.1
                        have p2375_2 := h2375c.2.2.1
                        have p2375_3 := h2375c.2.2.2
                        linarith only [hlam, p2375_0]
                    · linarith only [h2, h2368, h2374, h7, hlam]
                  · linarith only [h2136, h2368, h2373, hlam]
            · linarith only [h2134, h2135, h2136, h2368, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2416 | h2416
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2417 | h2417
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2418 | h2418
        · linarith only [h1, h2418, h7, hlam]
        · linarith only [h2135, h2416, h2418, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2421 | h2421
        · linarith only [h2135, h2416, h2421, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
        · linarith only [h2135, h2416, h2421, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2424 | h2424
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2425 | h2425
        · linarith only [h2135, h2424, h2425, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2427 | h2427
          · linarith only [h1953, h2135, h2424, h2427, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h2135, h2424, h2427, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2430 | h2430
        · linarith only [h1, h2430, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2432 | h2432
          · linarith only [h1, h1953, h2135, h2432, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2434 | h2434
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2435 | h2435
              · linarith only [h2435, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2437 | h2437
                · linarith only [h1953, h2437, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2439 | h2439
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2440 | h2440
                    · rcases h0bigk with h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c | h2441c
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [hlam, p2441_0]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h2135, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h2135, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h1953, h2134, h2135, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h1953, h2135, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h0, hlam, p2441_0]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [hlam, p2441_0]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h2135, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h0, h1953, h2134, h2135, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h0, h1953, h2135, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h1, hlam, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h4, hlam, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [hlam, p2441_0]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h7, hlam, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h1953, hlam, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h2, hlam, p2441_0]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h5, hlam, p2441_0]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h2135, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [hlam, p2441_0]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h1953, h2135, h4, h7, hc12, hc34, hlam, hphi, ht23, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h3, hlam, p2441_0]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h6, hlam, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h2135, h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [h2134, hlam, p2441_1]
                      · have p2441_0 := h2441c.1
                        have p2441_1 := h2441c.2.1
                        have p2441_2 := h2441c.2.2.1
                        have p2441_3 := h2441c.2.2.2
                        linarith only [hlam, p2441_0]
                    · linarith only [h2135, h2440, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h2416, h2434, h2439, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2469 | h2469
              · linarith only [h0, h2134, h2430, h2434, h2469, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2471 | h2471
                · linarith only [h1953, h2471, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2473 | h2473
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2474 | h2474
                    · rcases h0bigk with h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [hlam, p2475_0]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2135, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2135, h2430, h2434, h2473, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2135, h2471, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h0, hlam, p2475_0]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [hlam, p2475_0]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2135, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h0, h2135, h2430, h2434, h2473, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h0, h2135, h2471, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h1, hlam, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h4, hlam, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [hlam, p2475_0]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h7, hlam, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h1953, hlam, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2, hlam, p2475_0]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h5, hlam, p2475_0]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2135, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [hlam, p2475_0]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2135, h2471, h6, h7, hc12, hc34, hlam, hphi, ht23, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h3, hlam, p2475_0]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h6, hlam, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2135, h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [h2134, hlam, p2475_1]
                      · have p2475_0 := h2475c.1
                        have p2475_1 := h2475c.2.1
                        have p2475_2 := h2475c.2.2.1
                        have p2475_3 := h2475c.2.2.2
                        linarith only [hlam, p2475_0]
                    · linarith only [h2473, h2474, h5, h7, hlam]
                  · linarith only [h2134, h2416, h2473, h7, hc12, hc34, hlam, hphi, ht23]

end R2N4
