import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_31S3
import Jsp000404.R1LeavesN7_31S4
import Jsp000404.R1LeavesN7_31S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h740 | h740
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h740
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h740

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1803 | h1803
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1804 | h1804
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1805 | h1805
      · linarith only [h0, h1805, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1807 | h1807
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1808 | h1808
          · linarith only [h1, h1808, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1810 | h1810
            · linarith only [h1810, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1812 | h1812
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1813 | h1813
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1814 | h1814
                  · linarith only [h0, h1805, h1814, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1816 | h1816
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1817 | h1817
                      · linarith only [h1, h1808, h1817, h3, hlam]
                      · linarith only [h0, h1812, h1817, h3, hc23, hc35, hlam, hphi]
                    · linarith only [h1807, h1808, h1816, hc13, hc35, hlam, hphi]
                · linarith only [h0, h1804, h1812, h1813, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h1803, h1805, h1812, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1823 | h1823
          · linarith only [h1807, h1823, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1825 | h1825
            · linarith only [h0, h1804, h1825, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1827 | h1827
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1828 | h1828
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1829 | h1829
                  · linarith only [h0, h1805, h1829, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1831 | h1831
                    · linarith only [h1, h1807, h1829, h1831, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1833 | h1833
                      · linarith only [h1, h1823, h1833, h3, hlam]
                      · linarith only [h0, h1827, h1833, h3, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1804, h1827, h1828, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h1803, h1805, h1827, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1838 | h1838
      · linarith only [h1804, h1838, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1840 | h1840
        · linarith only [h1803, h1804, h1840, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1842 | h1842
          · linarith only [h1803, h1804, h1842, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1844 | h1844
            · linarith only [h1844, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1846 | h1846
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1847 | h1847
                · linarith only [h0, h1804, h1847, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1849 | h1849
                  · linarith only [h1847, h1849, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1851 | h1851
                    · linarith only [h1, h1840, h1851, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1853 | h1853
                      · linarith only [h1, h1803, h1804, h1842, h1853, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · linarith only [h1846, h1847, h1853, h2, h3, hc23, hc35, hlam, hphi]
              · linarith only [h1803, h1804, h1844, h1846, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1857 | h1857
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1858 | h1858
      · linarith only [h1, h1803, h1858, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1860 | h1860
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1861 | h1861
          · linarith only [h1, h1861, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1863 | h1863
            · linarith only [h1803, h1857, h1861, h1863, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1865 | h1865
              · linarith only [h0, h1803, h1857, h1865, h3, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1867 | h1867
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1868 | h1868
                  · linarith only [h0, h1803, h1868, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1870 | h1870
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1871 | h1871
                      · linarith only [h1, h1868, h1871, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1873 | h1873
                        · linarith only [h1863, h1871, h1873, h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                        · linarith only [h1, h1865, h1867, h1873, h3, hc24, hc45, hlam, hphi]
                    · linarith only [h1, h1860, h1865, h1867, h1870, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h1803, h1857, h1861, h1867, hc12, hc35, hlam, hphi, ht23]
        · linarith only [h1803, h1857, h1860, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1879 | h1879
      · linarith only [h1857, h1879, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1881 | h1881
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1882 | h1882
          · linarith only [h1, h1882, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1884 | h1884
            · linarith only [h1881, h1882, h1884, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1886 | h1886
              · linarith only [h0, h1803, h1886, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1888 | h1888
                · linarith only [h0, h1857, h1888, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1890 | h1890
                  · linarith only [h0, h1857, h1879, h1890, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1892 | h1892
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1893 | h1893
                      · linarith only [h1, h1893, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1895 | h1895
                        · linarith only [h1, h1857, h1884, h1892, h1893, h1895, h3, hc02, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1892, h1895, h3, hc34, hc45, hlam, hphi]
                    · linarith only [h1881, h1882, h1892, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1899 | h1899
          · linarith only [h1881, h1899, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1901 | h1901
            · linarith only [h1901, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1903 | h1903
              · linarith only [h0, h1803, h1903, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1905 | h1905
                · linarith only [h0, h1857, h1905, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1907 | h1907
                  · linarith only [h0, h1803, h1907, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1909 | h1909
                    · linarith only [h1, h1803, h1881, h1907, h1909, h3, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1911 | h1911
                      · linarith only [h1, h1907, h1911, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1913 | h1913
                        · linarith only [h1901, h1911, h1913, h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1915 | h1915
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1916 | h1916
                            · linarith only [h0, h1911, h1916, h3, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1803, h1881, h1915, h1916, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1919 | h1919
                            · linarith only [h1915, h1919, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1921 | h1921
                              · linarith only [h1903, h1909, h1913, h1921, h2, h3, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1923 | h1923
                                · linarith only [h0, h1803, h1915, h1921, h1923, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h1803, h1915, h1923, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1926 | h1926
  · linarith only [h1926, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1928 | h1928
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1929 | h1929
      · linarith only [h0, h1929, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1931 | h1931
        · linarith only [h0, h1931, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1933 | h1933
          · linarith only [h1, h1933, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1935 | h1935
            · linarith only [h0, h1928, h1935, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1937 | h1937
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1939 | h1939
                  · linarith only [h0, h1929, h1939, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1941 | h1941
                    · linarith only [h0, h1926, h1931, h1941, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1943 | h1943
                      · linarith only [h0, h1933, h1937, h1938, h1943, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h0, h1938, h1943, h2, hc23, hc34, hlam, hphi]
                · linarith only [h1928, h1929, h1938, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1947 | h1947
                · linarith only [h0, h1937, h1947, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1928, h1937, h1947, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1950 | h1950
      · linarith only [h0, h1950, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1952 | h1952
        · linarith only [h1928, h1952, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1954 | h1954
          · linarith only [h1, h1954, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1956 | h1956
            · linarith only [h1954, h1956, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1958 | h1958
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1959 | h1959
                · linarith only [h0, h1926, h1928, h1959, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1961 | h1961
                  · linarith only [h0, h1950, h1958, h1961, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1963 | h1963
                    · linarith only [h1, h1952, h1959, h1961, h1963, h2, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1965 | h1965
                      · linarith only [h1, h1954, h1961, h1965, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1967 | h1967
                        · linarith only [h1, h1956, h1965, h1967, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1969 | h1969
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1970 | h1970
                            · linarith only [h0, h1965, h1970, h2, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1972 | h1972
                              · linarith only [h1970, h1972, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1974 | h1974
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1975 | h1975
                                  · rcases h0bigk with h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, h1926, h1961, h1969, h1970, hc12, hc34, hlam, hphi, ht23, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, h1926, h1928, h1961, h1969, h1970, hc12, hc34, hlam, hphi, ht23, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h2, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1926, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1928, hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1950, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1952, hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, h1928, h1972, h1975, hc12, hc34, hlam, hphi, ht23, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1954, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1956, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1, h1950, h1970, hc13, hc34, hlam, hphi, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      rcases p1976_3 (m.d 0 1) (by simp) with h1993 | h1993
                                      · linarith only [h1993, h2, hlam]
                                      · linarith only [h0, h1993, hlam]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      rcases p1976_3 (m.d 0 1) (by simp) with h1996 | h1996
                                      · linarith only [h1996, h2, hlam]
                                      · linarith only [h1, h1996, hlam]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1958, h1961, h1970, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1976_1, u5ehi4]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1, h1926, h1959, h1961, h1969, h1970, hc12, hc34, hlam, hphi, ht23, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      rcases p1976_3 (m.d 0 1) (by simp) with h2002 | h2002
                                      · linarith only [h1926, h2002, hlam]
                                      · linarith only [h0, h2002, hlam]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      rcases p1976_3 (m.d 0 1) (by simp) with h2005 | h2005
                                      · linarith only [h1926, h2005, hlam]
                                      · linarith only [h1, h2005, hlam]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1958, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                  · linarith only [h1, h1959, h1961, h1970, h1975, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1958, h1961, h1974, h2, hlam]
                          · linarith only [h1958, h1969, h2, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2013 | h2013
                · linarith only [h0, h1958, h2, h2013, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2015 | h2015
                  · linarith only [h1, h1958, h2, h2013, h2015, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2017 | h2017
                    · linarith only [h1, h1958, h2, h2013, h2017, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2019 | h2019
                      · linarith only [h1, h1958, h2, h2019, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2021 | h2021
                        · linarith only [h1, h1958, h2, h2021, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2023 | h2023
                          · linarith only [h1, h1958, h2, h2013, h2015, h2023, hc12, hc24, hlam, hphi]
                          · linarith only [h1, h2, h2013, h2023, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2026 | h2026
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2027 | h2027
    · linarith only [h1, h2027, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2029 | h2029
      · linarith only [h0, h1, h2029, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2031 | h2031
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2032 | h2032
          · linarith only [h0, h1, h2032, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2034 | h2034
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2035 | h2035
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2036 | h2036
                · linarith only [h0, h1, h2031, h2036, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2038 | h2038
                  · linarith only [h0, h1, h2029, h2038, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2040 | h2040
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2041 | h2041
                      · linarith only [h0, h2027, h2032, h2041, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2043 | h2043
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2044 | h2044
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2045 | h2045
                            · linarith only [h0, h2026, h2027, h2031, h2038, h2044, h2045, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h0, h2027, h2040, h2045, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h1, h2035, h2040, h2044, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h1, h2040, h2043, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h2029, h2031, h2040, hc12, hc23, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2051 | h2051
                · linarith only [h0, h1, h2031, h2051, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2053 | h2053
                  · linarith only [h0, h1, h2029, h2053, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2055 | h2055
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2056 | h2056
                      · linarith only [h0, h2056, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2058 | h2058
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2059 | h2059
                          · linarith only [h0, h1, h2035, h2053, h2059, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h2055, h2059, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h2055, h2058, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h2029, h2031, h2055, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1, h2031, h2034, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2065 | h2065
          · linarith only [h1, h2026, h2031, h2065, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2067 | h2067
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2068 | h2068
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2069 | h2069
                · linarith only [h1, h2026, h2069, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2071 | h2071
                  · linarith only [h0, h1, h2029, h2071, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2073 | h2073
                    · linarith only [h0, h2031, h2073, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2075 | h2075
                      · linarith only [h1, h2026, h2065, h2071, h2073, h2075, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2077 | h2077
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2078 | h2078
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2079 | h2079
                            · linarith only [h2026, h2027, h2071, h2078, h2079, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2081 | h2081
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2082 | h2082
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2083 | h2083
                                  · linarith only [h2026, h2027, h2073, h2079, h2083, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2085 | h2085
                                    · linarith only [h2026, h2027, h2077, h2083, h2085, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2027, h2075, h2083, hc02, hc45, hlam, hphi, ht23, ht34, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h1, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, h2027, h2031, h2075, h2083, hc12, hc45, hlam, hphi, ht23, ht34, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2027, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2029, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2031, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2065, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, h1, h2071, hc12, hc23, hlam, hphi, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        rcases p2087_3 (m.d 0 1) (by simp) with h2099 | h2099
                                        · linarith only [h1, h2099, hlam]
                                        · linarith only [h0, h2099, hlam]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        rcases p2087_3 (m.d 0 1) (by simp) with h2103 | h2103
                                        · linarith only [h1, h2103, hlam]
                                        · linarith only [h2026, h2103, hlam]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h1, h2068, h2071, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2087_1, u5ehi3]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2026, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, h2026, h2027, h2075, hc12, hc25, hlam, hphi, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2067, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2069, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, h2027, h2075, h2083, hc12, hc45, hlam, hphi, ht23, ht34, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        rcases p2087_3 (m.d 0 1) (by simp) with h2113 | h2113
                                        · linarith only [h2027, h2113, hlam]
                                        · linarith only [h0, h2113, hlam]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2068, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        rcases p2087_3 (m.d 0 1) (by simp) with h2117 | h2117
                                        · linarith only [h2027, h2117, hlam]
                                        · linarith only [h2026, h2117, hlam]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                · linarith only [h1, h2026, h2071, h2073, h2082, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h2026, h2068, h2071, h2077, h2081, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h1, h2026, h2068, h2078, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h1, h2068, h2077, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2125 | h2125
                · linarith only [h1, h2026, h2125, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2127 | h2127
                  · linarith only [h0, h1, h2068, h2127, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2129 | h2129
                    · linarith only [h0, h2031, h2129, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2131 | h2131
                      · linarith only [h0, h2031, h2131, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2133 | h2133
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2134 | h2134
                          · linarith only [h1, h2026, h2068, h2127, h2129, h2134, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h2026, h2129, h2134, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2026, h2129, h2133, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h2026, h2067, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2139 | h2139
    · linarith only [h1, h2139, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2141 | h2141
      · linarith only [h0, h1, h2141, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2143 | h2143
        · linarith only [h0, h2026, h2143, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2145 | h2145
          · linarith only [h0, h2026, h2145, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2147 | h2147
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2148 | h2148
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2149 | h2149
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2150 | h2150
                  · linarith only [h0, h2026, h2141, h2150, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2152 | h2152
                    · linarith only [h0, h2143, h2149, h2152, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2154 | h2154
                      · linarith only [h0, h1, h2145, h2150, h2154, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2156 | h2156
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2157 | h2157
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2158 | h2158
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2159 | h2159
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2160 | h2160
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2161 | h2161
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2162 | h2162
                                    · linarith only [h1, h2147, h2150, h2162, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                    · rcases h0bigk with h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h0, h2139, h2150, h2156, h2158, hc12, hc23, hlam, hphi, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h1, hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2026, hlam, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2139, hlam, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h0, hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2141, hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2143, hlam, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2145, hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h0, h1, h2150, hc12, hc23, hlam, hphi, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        rcases p2164_3 (m.d 0 1) (by simp) with h2176 | h2176
                                        · linarith only [h1, h2176, hlam]
                                        · linarith only [h0, h2176, hlam]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h0, h1, h2026, h2150, hc12, hc23, hlam, hphi, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h1, h2150, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2164_1, u5ehi0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h0, h2026, h2150, h2156, hc12, hc23, hlam, hphi, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        rcases p2164_3 (m.d 0 1) (by simp) with h2183 | h2183
                                        · linarith only [h2026, h2183, hlam]
                                        · linarith only [h0, h2183, hlam]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2147, hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2026, h2149, h2150, h2156, h2162, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2164_1, u5ehi3]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h0, h2139, h2150, h2156, h2158, hc12, hc23, hlam, hphi, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        rcases p2164_3 (m.d 0 1) (by simp) with h2190 | h2190
                                        · linarith only [h2139, h2190, hlam]
                                        · linarith only [h0, h2190, hlam]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2148, hlam, p2164_0]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [h2149, hlam, p2164_1]
                                      · have p2164_0 := h2164c.1
                                        have p2164_1 := h2164c.2.1
                                        have p2164_2 := h2164c.2.2.1
                                        have p2164_3 := h2164c.2.2.2
                                        linarith only [hlam, p2164_0]
                                  · linarith only [h0, h2026, h2152, h2161, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h2147, h2149, h2150, h2160, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · linarith only [h1, h2147, h2149, h2150, h2159, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h2026, h2149, h2158, hlam]
                          · linarith only [h1, h2148, h2157, hlam]
                        · linarith only [h1, h2147, h2156, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2202 | h2202
                  · linarith only [h0, h2026, h2149, h2202, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2204 | h2204
                    · linarith only [h0, h2026, h2149, h2204, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2206 | h2206
                      · linarith only [h0, h2026, h2149, h2206, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2208 | h2208
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2209 | h2209
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2210 | h2210
                            · linarith only [h0, h2026, h2149, h2202, h2208, h2210, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h2026, h2210, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h2148, h2209, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h2148, h2208, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2215 | h2215
                · linarith only [h2147, h2148, h2215, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2217 | h2217
                  · linarith only [h0, h1, h2148, h2217, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2219 | h2219
                    · linarith only [h0, h2026, h2143, h2219, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2221 | h2221
                      · linarith only [h0, h2026, h2147, h2148, h2221, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2223 | h2223
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2224 | h2224
                          · linarith only [h0, h2026, h2147, h2148, h2217, h2224, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h2224, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h2147, h2223, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2228 | h2228
              · linarith only [h2147, h2228, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2230 | h2230
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2231 | h2231
                  · linarith only [h0, h1, h2228, h2231, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2233 | h2233
                    · linarith only [h0, h1, h2143, h2228, h2233, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2235 | h2235
                      · linarith only [h0, h1, h2145, h2228, h2235, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2237 | h2237
                        · linarith only [h2147, h2230, h2231, h2237, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h0, h1, h2237, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2240 | h2240
                  · linarith only [h0, h1, h2147, h2230, h2240, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2242 | h2242
                    · linarith only [h0, h1, h2143, h2147, h2242, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2244 | h2244
                      · linarith only [h0, h1, h2145, h2147, h2230, h2244, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2246 | h2246
                        · linarith only [h0, h1, h2147, h2240, h2246, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h2246, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0 m hb0 hb2 hb3 hb5 h0

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
