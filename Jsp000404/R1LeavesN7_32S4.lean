import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1838 | h1838
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1839 | h1839
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1840 | h1840
      · linarith only [h0, h1, h1840, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1842 | h1842
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1843 | h1843
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1844 | h1844
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1845 | h1845
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1846 | h1846
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1847 | h1847
                  · linarith only [h1840, h1842, h1846, h1847, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1849 | h1849
                    · linarith only [h1, h1838, h1847, h1849, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1, h1842, h1846, h1847, h1849, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1852 | h1852
                  · linarith only [h0, h1840, h1852, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1854 | h1854
                    · linarith only [h1, h1838, h1852, h1854, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · rcases h0bigk with h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1, h1842, h1852, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1856_1, u4ehi2]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1, h1852, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1856_1, u4ehi0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1, h1852, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1856_1]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h0, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1840, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1844, hc02, hlam, hphi, ht0b, ht45, ht5b, p1856_1, u4ehi3]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h0, h1, h1845, h1852, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1856_1]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1, h1852, hc01, hc23, hlam, hphi, ht12, p1856_1]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1, h1852, hc02, hc23, hlam, hphi, p1856_1]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1, h1844, h1852, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1856_1, u4ehi3]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1, h1844, h1846, h1852, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1856_1, u4ehi3]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1838, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1842, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1844, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1846, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1839, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1843, hlam, p1856_1]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1845, hlam, p1856_0]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [h1844, hc05, hlam, hphi, ht0b, ht45, ht5b, p1856_1, u4ehi3]
                      · have p1856_0 := h1856c.1
                        have p1856_1 := h1856c.2.1
                        have p1856_2 := h1856c.2.2.1
                        have p1856_3 := h1856c.2.2.2
                        linarith only [hlam, p1856_0]
              · linarith only [h0, h1, h1843, h1845, hlam]
            · linarith only [h1, h1838, h1844, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1884 | h1884
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1885 | h1885
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1886 | h1886
                · linarith only [h1842, h1843, h1886, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1888 | h1888
                  · linarith only [h0, h1840, h1888, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1890 | h1890
                    · linarith only [h1, h1838, h1886, h1888, h1890, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1, h1842, h1888, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1892_1, u4ehi2]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1, h1842, h1888, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1892_1, u4ehi2]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1, h1888, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1892_1]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h0, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1840, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1842, hc02, hlam, hphi, ht0b, ht45, ht5b, p1892_1, u4ehi2]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1843, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1892_1]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1, h1888, hc02, hc23, hlam, hphi, p1892_1]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1, h1842, h1888, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1892_1, u4ehi2]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1, h1842, h1843, h1888, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1892_1, u4ehi2]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1838, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1842, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1884, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1886, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1839, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1839, h1842, hc01, hlam, hphi, ht0b, ht45, ht5b, p1892_1, u4ehi2]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1885, hlam, p1892_0]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [h1, h1839, h1842, h1888, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1892_1, u4ehi2]
                      · have p1892_0 := h1892c.1
                        have p1892_1 := h1892c.2.1
                        have p1892_2 := h1892c.2.2.1
                        have p1892_3 := h1892c.2.2.2
                        linarith only [hlam, p1892_0]
              · linarith only [h1, h1839, h1885, hlam]
            · linarith only [h1, h1838, h1884, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1920 | h1920
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1921 | h1921
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1922 | h1922
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1923 | h1923
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1924 | h1924
                  · linarith only [h0, h1, h1840, h1924, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1926 | h1926
                    · linarith only [h1, h1838, h1924, h1926, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h1, h1838, h1923, h1924, h1926, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h1842, h1920, h1923, hlam]
              · linarith only [h0, h1, h1920, h1922, hlam]
            · linarith only [h1, h1838, h1921, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1932 | h1932
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1933 | h1933
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1934 | h1934
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1935 | h1935
                  · linarith only [h0, h1, h1840, h1935, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1937 | h1937
                    · linarith only [h1, h1838, h1935, h1937, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h1, h1838, h1934, h1935, h1937, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1940 | h1940
                  · linarith only [h0, h1840, h1940, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1942 | h1942
                    · linarith only [h1838, h1934, h1942, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1, h1940, hc02, hc23, hlam, hphi, p1944_1]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1, h1932, h1940, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1944_1, u4ehi3]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1, h1940, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1944_1]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h0, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1840, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1842, hlam, p1944_1]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1920, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1, h1940, hc01, hc23, hlam, hphi, ht12, p1944_1]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h0, h1, h1940, hc12, hc23, hlam, hphi, p1944_1]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1, h1932, h1940, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1944_1, u4ehi3]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h0, h1, h1920, h1940, hc12, hc23, hlam, hphi, p1944_1]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1838, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h0, h1, h1838, h1940, hc12, hc23, hlam, hphi, p1944_1]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1932, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1934, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1839, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h0, h1, h1839, h1940, hc12, hc23, hlam, hphi, p1944_1]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1933, hlam, p1944_0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [h1, h1839, h1940, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1944_1, u4ehi0]
                      · have p1944_0 := h1944c.1
                        have p1944_1 := h1944c.2.1
                        have p1944_2 := h1944c.2.2.1
                        have p1944_3 := h1944c.2.2.2
                        linarith only [hlam, p1944_0]
              · linarith only [h1, h1839, h1933, hlam]
            · linarith only [h1, h1838, h1932, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1972 | h1972
      · linarith only [h0, h1, h1972, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1974 | h1974
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1975 | h1975
          · linarith only [h0, h1839, h1975, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1977 | h1977
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1978 | h1978
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1979 | h1979
                · linarith only [h0, h1839, h1974, h1979, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1981 | h1981
                  · linarith only [h0, h1, h1972, h1981, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1983 | h1983
                    · linarith only [h1838, h1979, h1983, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h0, h1839, h1974, h1983, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1986 | h1986
                · linarith only [h0, h1839, h1974, h1986, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1988 | h1988
                  · linarith only [h0, h1839, h1972, h1988, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1990 | h1990
                    · linarith only [h1, h1838, h1978, h1986, h1990, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · linarith only [h1838, h1839, h1990, hc45, hlam, hphi, u4ehi1]
            · linarith only [h1, h1838, h1977, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1994 | h1994
          · linarith only [h1838, h1839, h1974, h1994, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1996 | h1996
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1997 | h1997
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1998 | h1998
                · linarith only [h1838, h1839, h1998, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2000 | h2000
                  · linarith only [h0, h1, h1972, h2000, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2002 | h2002
                    · linarith only [h1838, h1998, h2002, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h1838, h1839, h2002, hc45, hlam, hphi, u4ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2005 | h2005
                · linarith only [h1838, h1839, h2005, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2007 | h2007
                  · linarith only [h0, h1, h1972, h2007, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2009 | h2009
                    · linarith only [h1, h1838, h1997, h2005, h2009, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · linarith only [h1838, h1839, h2009, hc45, hlam, hphi, u4ehi1]
            · linarith only [h1, h1838, h1996, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2013 | h2013
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2014 | h2014
      · linarith only [h0, h1, h2014, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2016 | h2016
        · linarith only [h0, h1838, h2016, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2018 | h2018
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2019 | h2019
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2020 | h2020
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2021 | h2021
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2022 | h2022
                  · linarith only [h0, h1, h2014, h2022, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2024 | h2024
                    · rcases h0bigk with h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h1, h2013, h2018, h2022, h2024, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2025_1, u4ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h1, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h1838, hlam, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h1, h2013, h2022, h2024, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2025_1, u4ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h0, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2014, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2016, hlam, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2013, h2024, hc02, hlam, hphi, ht0b, ht45, ht5b, p2025_1, u4ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h1, h2022, hc02, hc23, hlam, hphi, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h1, h1838, h2013, h2022, h2024, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2025_1, u4ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h1, h2013, h2022, h2024, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2025_1, u4ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2013, h2024, hc04, hlam, hphi, ht0b, ht45, ht5b, p2025_1, u4ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2013, h2016, h2018, h2024, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2025_1, u4ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2019, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h1, h2013, h2019, h2022, h2024, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2025_1, u4ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2013, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2018, hlam, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2020, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2021, hlam, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                    · linarith only [h0, h1838, h2024, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h0, h1838, h2018, h2021, hlam]
              · linarith only [h0, h1, h2018, h2020, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2054 | h2054
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2055 | h2055
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2056 | h2056
                  · linarith only [h0, h1, h2019, h2056, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2058 | h2058
                    · rcases h0bigk with h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h1, h2019, hc02, hc34, hlam, hphi, ht23, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h1, hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h1838, hlam, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h1, h2019, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h0, hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2014, hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2016, hlam, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h0, h1, h2013, h2019, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2019, hc01, hc34, hlam, hphi, ht12, ht23, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2019, hc02, hc34, hlam, hphi, ht23, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2019, hlam, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2013, h2019, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2016, h2018, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2019, hc03, hc34, hlam, hphi, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2019, h2055, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2059_1, u4ehi4]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2013, hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2018, hlam, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2054, hlam, p2059_0]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [h2055, hlam, p2059_1]
                      · have p2059_0 := h2059c.1
                        have p2059_1 := h2059c.2.1
                        have p2059_2 := h2059c.2.2.1
                        have p2059_3 := h2059c.2.2.2
                        linarith only [hlam, p2059_0]
                    · linarith only [h0, h1838, h2018, h2055, h2058, hlam]
                · linarith only [h0, h1838, h2018, h2055, hlam]
              · linarith only [h0, h1, h2018, h2054, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2088 | h2088
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2089 | h2089
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2090 | h2090
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2091 | h2091
                  · linarith only [h0, h1, h2014, h2091, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2093 | h2093
                    · rcases h0bigk with h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c | h2094c
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h0, h1, h2091, hc12, hc23, hlam, hphi, p2094_1]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h1, hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h1838, hlam, p2094_1]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h1, h2091, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2094_1]
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
                        linarith only [h2014, hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h2016, hlam, p2094_1]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h2018, hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h2013, hc03, hc15, hlam, hphi, ht0b, ht5b, p2094_1]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h0, h1, h2091, hc12, hc23, hlam, hphi, p2094_1]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h1, h1838, h2013, h2091, h2093, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2094_1, u4ehi4]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h1, h2013, h2091, h2093, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2094_1, u4ehi4]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h2013, h2093, hc04, hlam, hphi, ht0b, ht45, ht5b, p2094_1, u4ehi4]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h0, h2016, hc12, hc24, hlam, hphi, p2094_1]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h2088, hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h1, h2013, h2088, h2091, h2093, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2094_1, u4ehi4]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h2013, hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h0, h1, h2013, h2091, hc12, hc23, hlam, hphi, p2094_1]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h2089, hlam, p2094_0]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [h2090, hlam, p2094_1]
                      · have p2094_0 := h2094c.1
                        have p2094_1 := h2094c.2.1
                        have p2094_2 := h2094c.2.2.1
                        have p2094_3 := h2094c.2.2.2
                        linarith only [hlam, p2094_0]
                    · linarith only [h0, h1838, h2093, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1838, h2013, h2090, hlam]
              · linarith only [h1, h2013, h2089, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2123 | h2123
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2124 | h2124
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2125 | h2125
                  · linarith only [h0, h1, h2088, h2125, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2127 | h2127
                    · rcases h0bigk with h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c | h2128c
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [hlam, p2128_0]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h1, h2088, hc02, hc34, hlam, hphi, ht23, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h1, hlam, p2128_0]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h1838, hlam, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h1, h2088, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2128_1]
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
                        linarith only [h2014, hlam, p2128_0]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2016, hlam, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2018, hlam, p2128_0]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2088, hc01, hc34, hlam, hphi, ht12, ht23, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h0, h2088, hc12, hc34, hlam, hphi, ht23, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [hlam, p2128_0]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2088, hlam, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2013, h2088, h2127, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2128_1, u4ehi4]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2013, h2127, hc04, hlam, hphi, ht0b, ht45, ht5b, p2128_1, u4ehi4]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h0, h2016, hc12, hc24, hlam, hphi, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2088, hc03, hc34, hlam, hphi, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [hlam, p2128_0]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2013, h2088, h2127, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2128_1, u4ehi4]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2013, hlam, p2128_0]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h0, h1, h2013, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2123, hlam, p2128_0]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [h2124, hlam, p2128_1]
                      · have p2128_0 := h2128c.1
                        have p2128_1 := h2128c.2.1
                        have p2128_2 := h2128c.2.2.1
                        have p2128_3 := h2128c.2.2.2
                        linarith only [hlam, p2128_0]
                    · linarith only [h0, h1838, h2127, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1, h2013, h2088, h2124, hlam]
              · linarith only [h1, h2013, h2123, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2157 | h2157
      · linarith only [h0, h1, h2157, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2159 | h2159
        · linarith only [h0, h1838, h2159, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2161 | h2161
          · linarith only [h0, h2013, h2161, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2163 | h2163
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2164 | h2164
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2165 | h2165
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2166 | h2166
                  · linarith only [h0, h1, h2157, h2166, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2168 | h2168
                    · rcases h0bigk with h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, h1, h2166, hc12, hc23, hlam, hphi, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h1, hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h1838, hlam, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h2013, hlam, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h2157, hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h2159, hlam, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h2161, hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, h1, h2166, hc12, hc23, hlam, hphi, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h1, h2165, h2166, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2169_1, u4ehi4]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, h1, h2013, h2166, hc12, hc23, hlam, hphi, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, h2159, hc12, hc24, hlam, hphi, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h2163, hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, h1, h2013, h2163, h2166, hc12, hc23, hlam, hphi, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h0, h2161, hc12, hc25, hlam, hphi, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h2164, hlam, p2169_0]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [h2165, hlam, p2169_1]
                      · have p2169_0 := h2169c.1
                        have p2169_1 := h2169c.2.1
                        have p2169_2 := h2169c.2.2.1
                        have p2169_3 := h2169c.2.2.2
                        linarith only [hlam, p2169_0]
                    · linarith only [h0, h1838, h2168, hc12, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2196 | h2196
                  · linarith only [h0, h2157, h2196, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2198 | h2198
                    · rcases h0bigk with h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c | h2199c
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h1838, h2165, h2198, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h1, hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h1838, hlam, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h2013, hlam, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h0, hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h2157, hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h2159, hlam, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h2161, hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h0, h1, h2196, hc12, hc23, hlam, hphi, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h1, h2196, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2199_1, u4ehi0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h0, h1, h1838, h2165, h2196, hc12, hc23, hlam, hphi, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h0, h2159, hc12, hc24, hlam, hphi, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h2163, hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h2165, hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h0, h2013, h2198, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h0, h2161, hc12, hc25, hlam, hphi, p2199_1]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h2164, hlam, p2199_0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [h2165, h2198, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2199_1, u4ehi0]
                      · have p2199_0 := h2199c.1
                        have p2199_1 := h2199c.2.1
                        have p2199_2 := h2199c.2.2.1
                        have p2199_3 := h2199c.2.2.2
                        linarith only [hlam, p2199_0]
                    · linarith only [h0, h1838, h2198, hc12, hc45, hlam, hphi, ht23, ht34]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2226 | h2226
                · linarith only [h2163, h2164, h2226, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2228 | h2228
                  · linarith only [h0, h1, h2164, h2228, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2230 | h2230
                    · rcases h0bigk with h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h1838, h2226, h2230, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h1, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h1838, hlam, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2013, hlam, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2157, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2159, hlam, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2161, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2164, hc01, hc35, hlam, hphi, ht12, ht23, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2164, hc12, hc35, hlam, hphi, ht23, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h1838, h2164, hc12, hc35, hlam, hphi, ht23, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2164, hlam, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2226, h2230, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2226, h2230, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2163, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2226, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2161, hc12, hc25, hlam, hphi, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2164, hc03, hc35, hlam, hphi, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2226, h2230, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2231_1, u4ehi0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                    · linarith only [h0, h1838, h2230, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2258 | h2258
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2259 | h2259
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2260 | h2260
                  · linarith only [h0, h1, h2163, h2260, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2262 | h2262
                    · rcases h0bigk with h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h1, hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h1838, hlam, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2013, hlam, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h0, hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2157, hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2159, hlam, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2161, hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2163, hc01, hc34, hlam, hphi, ht12, ht23, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h0, h2163, hc12, hc34, hlam, hphi, ht23, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2163, hlam, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2163, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h0, h2159, hc12, hc24, hlam, hphi, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2163, hc03, hc34, hlam, hphi, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h0, h2013, h2163, hc12, hc34, hlam, hphi, ht23, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h0, h2258, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h0, h1, h2258, h2260, hc12, hc23, hlam, hphi, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2258, hlam, p2263_0]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [h2259, hlam, p2263_1]
                      · have p2263_0 := h2263c.1
                        have p2263_1 := h2263c.2.1
                        have p2263_2 := h2263c.2.2.1
                        have p2263_3 := h2263c.2.2.2
                        linarith only [hlam, p2263_0]
                    · linarith only [h0, h1838, h2163, h2258, h2259, h2262, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2163, h2258, h2259, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2291 | h2291
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2292 | h2292
                  · linarith only [h0, h1, h2258, h2292, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2294 | h2294
                    · rcases h0bigk with h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [hlam, p2295_0]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h1, h2258, hc02, hc35, hlam, hphi, ht23, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h1, hlam, p2295_0]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h1838, hlam, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2013, hlam, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h0, hlam, p2295_0]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [hlam, p2295_0]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2157, hlam, p2295_0]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2159, hlam, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2161, hlam, p2295_0]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2258, hc01, hc35, hlam, hphi, ht12, ht23, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h0, h2258, hc12, hc35, hlam, hphi, ht23, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [hlam, p2295_0]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2163, hlam, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2258, hlam, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h0, h2159, hc12, hc24, hlam, hphi, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2163, hc03, hc34, hlam, hphi, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [hlam, p2295_0]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h0, h2013, h2163, hc12, hc34, hlam, hphi, ht23, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h0, h2161, hc12, hc25, hlam, hphi, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h0, h1, h2258, hc12, hc35, hlam, hphi, ht23, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [h2291, hlam, p2295_1]
                      · have p2295_0 := h2295c.1
                        have p2295_1 := h2295c.2.1
                        have p2295_2 := h2295c.2.2.1
                        have p2295_3 := h2295c.2.2.2
                        linarith only [hlam, p2295_0]
                    · linarith only [h0, h1838, h2294, hc12, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2322 | h2322
                  · linarith only [h0, h1838, h2291, h2322, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2324 | h2324
                    · rcases h0bigk with h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h1, hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h1838, hlam, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2013, hlam, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2157, hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2159, hlam, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2161, hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, h1, h2322, hc12, hc23, hlam, hphi, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2163, hlam, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2258, hlam, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, h2291, h2324, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, h2291, h2324, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2291, h2324, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2291, hlam, p2325_0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, h2291, h2324, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, h2291, h2324, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h0, h1, h2291, h2324, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2325_1]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [h2291, h2324, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2325_1, u4ehi0]
                      · have p2325_0 := h2325c.1
                        have p2325_1 := h2325c.2.1
                        have p2325_2 := h2325c.2.2.1
                        have p2325_3 := h2325c.2.2.2
                        linarith only [hlam, p2325_0]
                    · linarith only [h0, h1838, h2324, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_14_H_I_L_R_x0_x0 m hb0 hb4 h0 h1
  · exact r1l7_20_14_H_I_L_R_x0_x1 m hb0 hb4 h0 h1

end R2N4
