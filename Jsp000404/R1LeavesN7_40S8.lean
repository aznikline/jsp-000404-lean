import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h1810 | h1810
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1811 | h1811
    · linarith only [h1811, h4, h5, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1813 | h1813
      · linarith only [h1810, h1813, h4, h5, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1815 | h1815
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1816 | h1816
          · linarith only [h1810, h1816, h2, h4, h5, hc12, hlam, hphi, u1ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1818 | h1818
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1819 | h1819
              · linarith only [h1810, h1811, h1819, h2, hc13, hlam, hphi, u1ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1821 | h1821
                · linarith only [h1813, h1821, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1823 | h1823
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1824 | h1824
                    · linarith only [h0, h1, h1811, h1815, h1824, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1826 | h1826
                      · linarith only [h0, h1813, h1815, h1823, h1824, h1826, h2, h5, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                      · linarith only [h0, h1815, h1823, h1826, h5, hc34, hc45, hlam, hphi]
                  · linarith only [h1810, h1811, h1823, hc23, hc35, hlam, hphi]
            · linarith only [h1810, h1811, h1818, hc13, hc35, hlam, hphi]
        · linarith only [h1815, h4, h5, hc25, hlam, hphi, ht12, u1ehi1]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1832 | h1832
    · linarith only [h1832, h4, h5, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1834 | h1834
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1835 | h1835
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1836 | h1836
          · linarith only [h0, h1836, h5, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1838 | h1838
            · linarith only [h1, h1810, h1838, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1840 | h1840
              · linarith only [h1, h1832, h1840, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1842 | h1842
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1843 | h1843
                  · linarith only [h1, h1810, h1843, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1845 | h1845
                    · linarith only [h1, h1832, h1835, h1845, hc12, hlam, hphi, u1ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1847 | h1847
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1848 | h1848
                        · rcases h3bigk with h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c | h1849c
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1847, h4, h5, hc24, hlam, hphi, ht12, p1849_1, u1ehi2]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1843, h1847, h4, h5, hc23, hc34, hlam, hphi, p1849_1]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1810, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1832, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1, h1843, h1847, h4, h5, hc23, hc34, hlam, hphi, p1849_1]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1838, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1840, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h4, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1835, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1843, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1845, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1, hc34, hlam, hphi, ht12, ht23, p1849_1, u1ehi2]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [hc34, hlam, hphi, ht12, ht23, p1849_1, u1ehi2]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            rcases p1849_3 (m.d 0 3) (by simp) with h1867 | h1867
                            · linarith only [h1810, h1867, hlam]
                            · linarith only [h1867, h4, hlam]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1845, h5, hc02, hc34, hlam, hphi, ht23, p1849_1]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1, hc35, hlam, hphi, ht12, ht23, p1849_1, u1ehi2]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [hc35, hlam, hphi, ht12, ht23, p1849_1, u1ehi2]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            rcases p1849_3 (m.d 0 3) (by simp) with h1874 | h1874
                            · linarith only [h1832, h1874, hlam]
                            · linarith only [h1874, h4, hlam]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [h1848, hlam, p1849_0]
                          · have p1849_0 := h1849c.1
                            have p1849_1 := h1849c.2.1
                            have p1849_2 := h1849c.2.2.1
                            have p1849_3 := h1849c.2.2.2
                            linarith only [hlam, p1849_0]
                        · linarith only [h1, h1810, h1842, h1848, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · linarith only [h1, h1842, h1847, h2, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                · linarith only [h1810, h1834, h1842, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h1835, h4, h5, hc12, hc25, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1883 | h1883
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1884 | h1884
          · linarith only [h0, h1884, h5, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1886 | h1886
            · linarith only [h1, h1810, h1886, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1888 | h1888
              · linarith only [h1, h1832, h1888, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1890 | h1890
                · linarith only [h1834, h1890, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1892 | h1892
                  · linarith only [h0, h1, h1810, h1883, h1892, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1894 | h1894
                    · linarith only [h0, h1, h1832, h1883, h1894, h5, hc25, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1896 | h1896
                      · linarith only [h1, h1810, h1834, h1896, hc24, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1898 | h1898
                        · linarith only [h0, h1883, h1896, h1898, h5, hc23, hc34, hlam, hphi]
                        · linarith only [h1, h1810, h1898, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · linarith only [h1883, h4, h5, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1902 | h1902
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1903 | h1903
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1904 | h1904
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1905 | h1905
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1906 | h1906
          · linarith only [h0, h1902, h1906, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1908 | h1908
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1909 | h1909
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1910 | h1910
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1911 | h1911
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1912 | h1912
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1913 | h1913
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1914 | h1914
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1915 | h1915
                          · rcases h3bigk with h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1909, h1915, hc03, hc45, hlam, hphi, ht0b, ht5b, p1916_1]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h4, hlam, p1916_1]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              rcases p1916_3 (m.d 0 3) (by simp) with h1920 | h1920
                              · rcases p1916_3 (m.d 1 3) (by simp) with h1921 | h1921
                                · linarith only [h1, h1921, hlam]
                                · linarith only [h1909, h1921, hlam]
                              · linarith only [h1920, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              rcases p1916_3 (m.d 0 3) (by simp) with h1925 | h1925
                              · rcases p1916_3 (m.d 1 3) (by simp) with h1926 | h1926
                                · linarith only [h1, h1926, hlam]
                                · linarith only [h1910, h1926, hlam]
                              · linarith only [h1925, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1906, hlam, p1916_1]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1, h1915, hc01, hc45, hlam, hphi, ht0b, ht5b, p1916_1]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              rcases p1916_3 (m.d 0 3) (by simp) with h1934 | h1934
                              · rcases p1916_3 (m.d 1 3) (by simp) with h1935 | h1935
                                · rcases p1916_3 (m.d 2 3) (by simp) with h1936 | h1936
                                  · rcases p1916_3 (m.d 3 4) (by simp) with h1937 | h1937
                                    · linarith only [h1909, h1937, hlam]
                                    · linarith only [h1915, h1937, hlam]
                                  · linarith only [h1913, h1936, hlam]
                                · linarith only [h1935, hlam, p1916_0]
                              · linarith only [h1904, h1934, hlam]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1, hc23, hlam, hphi, ht12, p1916_1, u1ehi2]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [hc23, hlam, hphi, ht12, p1916_1, u1ehi2]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              rcases p1916_3 (m.d 0 3) (by simp) with h1946 | h1946
                              · linarith only [h1946, h4, hlam]
                              · linarith only [h1903, h1946, hlam]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              rcases p1916_3 (m.d 0 3) (by simp) with h1949 | h1949
                              · linarith only [h1949, h4, hlam]
                              · linarith only [h1904, h1949, hlam]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1903, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1909, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1912, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1, h1909, hc01, hc35, hlam, hphi, ht0b, ht5b, p1916_1]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1904, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1910, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1913, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [h1915, hlam, p1916_0]
                            · have p1916_0 := h1916c.1
                              have p1916_1 := h1916c.2.1
                              have p1916_2 := h1916c.2.2.1
                              have p1916_3 := h1916c.2.2.2
                              linarith only [hlam, p1916_0]
                          · rcases h3bigk with h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c | h1962c
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h4, hc23, hlam, hphi, ht12, p1962_1, u1ehi2]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h4, hlam, p1962_1]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              rcases p1962_3 (m.d 0 3) (by simp) with h1966 | h1966
                              · rcases p1962_3 (m.d 1 3) (by simp) with h1967 | h1967
                                · linarith only [h1, h1967, hlam]
                                · linarith only [h1909, h1967, hlam]
                              · linarith only [h1966, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              rcases p1962_3 (m.d 0 3) (by simp) with h1971 | h1971
                              · rcases p1962_3 (m.d 1 3) (by simp) with h1972 | h1972
                                · linarith only [h1, h1972, hlam]
                                · linarith only [h1910, h1972, hlam]
                              · linarith only [h1971, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1906, hlam, p1962_1]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              rcases p1962_3 (m.d 0 3) (by simp) with h1979 | h1979
                              · rcases p1962_3 (m.d 1 3) (by simp) with h1980 | h1980
                                · rcases p1962_3 (m.d 2 3) (by simp) with h1981 | h1981
                                  · rcases p1962_3 (m.d 3 4) (by simp) with h1982 | h1982
                                    · linarith only [h1982, hlam, p1962_0]
                                    · rcases p1962_3 (m.d 3 5) (by simp) with h1984 | h1984
                                      · linarith only [h1910, h1984, hlam]
                                      · linarith only [h1915, h1984, hlam]
                                  · linarith only [h1912, h1981, hlam]
                                · linarith only [h1980, hlam, p1962_0]
                              · linarith only [h1903, h1979, hlam]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              rcases p1962_3 (m.d 0 3) (by simp) with h1990 | h1990
                              · rcases p1962_3 (m.d 1 3) (by simp) with h1991 | h1991
                                · rcases p1962_3 (m.d 2 3) (by simp) with h1992 | h1992
                                  · rcases p1962_3 (m.d 3 4) (by simp) with h1993 | h1993
                                    · linarith only [h1909, h1993, hlam]
                                    · rcases p1962_3 (m.d 3 5) (by simp) with h1995 | h1995
                                      · linarith only [h1995, hlam, p1962_0]
                                      · rcases h5bigk with h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1902, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1902, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1902, h1915, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1902, h1915, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h3, hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1914, h1915, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1902, h1915, h3, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1902, h1915, h3, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1902, hlam, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1908, hlam, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1902, h1915, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h0, h1908, h1915, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1904, hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1910, hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1913, hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1915, hlam, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1905, hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1911, hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1914, hlam, p1997_0]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [h1915, hc34, hc45, hlam, hphi, p1997_1]
                                        · have p1997_0 := h1997c.1
                                          have p1997_1 := h1997c.2.1
                                          have p1997_2 := h1997c.2.2.1
                                          have p1997_3 := h1997c.2.2.2
                                          linarith only [hlam, p1997_0]
                                  · linarith only [h1913, h1992, hlam]
                                · linarith only [h1991, hlam, p1962_0]
                              · linarith only [h1904, h1990, hlam]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1, h1906, hc23, hlam, hphi, ht12, p1962_1, u1ehi1]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1906, hc23, hlam, hphi, ht12, p1962_1, u1ehi1]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h0, h1908, h1914, h1915, h4, hlam, p1962_2]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              rcases p1962_3 (m.d 0 3) (by simp) with h2030 | h2030
                              · linarith only [h2030, h4, hlam]
                              · linarith only [h1904, h2030, hlam]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1903, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1909, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1912, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1915, hlam, p1962_1]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1904, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1910, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1913, hlam, p1962_0]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [h1, h1910, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1962_1]
                            · have p1962_0 := h1962c.1
                              have p1962_1 := h1962c.2.1
                              have p1962_2 := h1962c.2.2.1
                              have p1962_3 := h1962c.2.2.2
                              linarith only [hlam, p1962_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2043 | h2043
                          · linarith only [h1, h1909, h1914, h2043, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h3bigk with h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c | h2045c
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h4, hc23, hlam, hphi, ht12, p2045_1, u1ehi2]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h4, hlam, p2045_1]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              rcases p2045_3 (m.d 0 3) (by simp) with h2049 | h2049
                              · rcases p2045_3 (m.d 1 3) (by simp) with h2050 | h2050
                                · linarith only [h1, h2050, hlam]
                                · linarith only [h1909, h2050, hlam]
                              · linarith only [h2049, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              rcases p2045_3 (m.d 0 3) (by simp) with h2054 | h2054
                              · rcases p2045_3 (m.d 1 3) (by simp) with h2055 | h2055
                                · linarith only [h1, h2055, hlam]
                                · linarith only [h1910, h2055, hlam]
                              · linarith only [h2054, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1906, hlam, p2045_1]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              rcases p2045_3 (m.d 0 3) (by simp) with h2062 | h2062
                              · rcases p2045_3 (m.d 1 3) (by simp) with h2063 | h2063
                                · rcases p2045_3 (m.d 2 3) (by simp) with h2064 | h2064
                                  · rcases p2045_3 (m.d 3 4) (by simp) with h2065 | h2065
                                    · linarith only [h2065, hlam, p2045_0]
                                    · rcases p2045_3 (m.d 3 5) (by simp) with h2067 | h2067
                                      · linarith only [h1910, h2067, hlam]
                                      · linarith only [h2043, h2067, hlam]
                                  · linarith only [h1912, h2064, hlam]
                                · linarith only [h2063, hlam, p2045_0]
                              · linarith only [h1903, h2062, hlam]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              rcases p2045_3 (m.d 0 3) (by simp) with h2073 | h2073
                              · rcases p2045_3 (m.d 1 3) (by simp) with h2074 | h2074
                                · rcases p2045_3 (m.d 2 3) (by simp) with h2075 | h2075
                                  · rcases p2045_3 (m.d 3 4) (by simp) with h2076 | h2076
                                    · linarith only [h1909, h2076, hlam]
                                    · rcases p2045_3 (m.d 3 5) (by simp) with h2078 | h2078
                                      · linarith only [h2078, hlam, p2045_0]
                                      · rcases h5bigk with h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1902, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1902, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1902, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1902, h1912, h1914, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h3, hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h0, h1908, h1913, hc01, hc35, hlam, hphi, ht0b, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h0, h1908, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h0, h1908, h1912, h1914, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1902, hlam, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1908, hlam, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1902, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1914, hlam, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1904, hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1910, hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1913, hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h2043, hlam, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1905, hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1911, hlam, p2080_0]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1905, hc04, hc25, hlam, hphi, ht0b, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [h1, h1909, h1911, hc01, hc35, hlam, hphi, ht0b, ht5b, p2080_1]
                                        · have p2080_0 := h2080c.1
                                          have p2080_1 := h2080c.2.1
                                          have p2080_2 := h2080c.2.2.1
                                          have p2080_3 := h2080c.2.2.2
                                          linarith only [hlam, p2080_0]
                                  · linarith only [h1913, h2075, hlam]
                                · linarith only [h2074, hlam, p2045_0]
                              · linarith only [h1904, h2073, hlam]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1, hc23, hlam, hphi, ht12, p2045_1, u1ehi2]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1909, hc23, hlam, hphi, ht12, p2045_1, u1ehi3]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              rcases p2045_3 (m.d 0 3) (by simp) with h2112 | h2112
                              · linarith only [h2112, h4, hlam]
                              · linarith only [h1903, h2112, hlam]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              rcases p2045_3 (m.d 0 3) (by simp) with h2115 | h2115
                              · linarith only [h2115, h4, hlam]
                              · linarith only [h1904, h2115, hlam]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1903, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1909, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1912, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h2043, hlam, p2045_1]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1904, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1910, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1913, hlam, p2045_0]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [h1, h1910, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2045_1]
                            · have p2045_0 := h2045c.1
                              have p2045_1 := h2045c.2.1
                              have p2045_2 := h2045c.2.2.1
                              have p2045_3 := h2045c.2.2.2
                              linarith only [hlam, p2045_0]
                      · linarith only [h1902, h1910, h1913, h3, h4, hlam]
                    · linarith only [h0, h1912, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h1903, h1905, h1911, h4, hc23, hlam, hphi, ht12, u1ehi3]
                · linarith only [h1904, h1910, h4, hc23, hlam, hphi, ht12, u1ehi2]
              · linarith only [h1903, h1906, h1909, h4, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h1902, h1908, h4, hc23, hlam, hphi, ht12, u1ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2134 | h2134
          · linarith only [h0, h1902, h2134, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2136 | h2136
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2137 | h2137
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2138 | h2138
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2139 | h2139
                  · linarith only [h1905, h2, h2139, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2141 | h2141
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2142 | h2142
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2143 | h2143
                        · linarith only [h1905, h2, h2143, hc24, hlam, hphi, ht12, u1ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2145 | h2145
                          · linarith only [h1905, h2, h2141, h2145, hc24, hlam, hphi, ht12, u1ehi3]
                          · rcases h3bigk with h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c | h2147c
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h2134, h4, hc23, hlam, hphi, ht12, p2147_1, u1ehi1]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h4, hlam, p2147_1]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              rcases p2147_3 (m.d 0 3) (by simp) with h2151 | h2151
                              · rcases p2147_3 (m.d 1 3) (by simp) with h2152 | h2152
                                · linarith only [h1, h2152, hlam]
                                · linarith only [h2137, h2152, hlam]
                              · linarith only [h2151, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              rcases p2147_3 (m.d 0 3) (by simp) with h2156 | h2156
                              · rcases p2147_3 (m.d 1 3) (by simp) with h2157 | h2157
                                · linarith only [h1, h2157, hlam]
                                · linarith only [h2138, h2157, hlam]
                              · linarith only [h2156, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h1, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h2134, hlam, p2147_1]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              rcases p2147_3 (m.d 0 3) (by simp) with h2164 | h2164
                              · rcases p2147_3 (m.d 1 3) (by simp) with h2165 | h2165
                                · rcases p2147_3 (m.d 2 3) (by simp) with h2166 | h2166
                                  · rcases p2147_3 (m.d 3 4) (by simp) with h2167 | h2167
                                    · linarith only [h2167, hlam, p2147_0]
                                    · rcases p2147_3 (m.d 3 5) (by simp) with h2169 | h2169
                                      · linarith only [h2138, h2169, hlam]
                                      · linarith only [h2145, h2169, hlam]
                                  · linarith only [h2141, h2166, hlam]
                                · linarith only [h2165, hlam, p2147_0]
                              · linarith only [h1903, h2164, hlam]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              rcases p2147_3 (m.d 0 3) (by simp) with h2175 | h2175
                              · rcases p2147_3 (m.d 1 3) (by simp) with h2176 | h2176
                                · rcases p2147_3 (m.d 2 3) (by simp) with h2177 | h2177
                                  · rcases p2147_3 (m.d 3 4) (by simp) with h2178 | h2178
                                    · linarith only [h2137, h2178, hlam]
                                    · rcases p2147_3 (m.d 3 5) (by simp) with h2180 | h2180
                                      · linarith only [h2180, hlam, p2147_0]
                                      · rcases h5bigk with h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [hlam, p2182_0]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h1902, h2139, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2182_1, u1ehi3]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h1902, h2143, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h1902, h2145, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h1905, hlam, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h3, hlam, p2182_0]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [hlam, p2182_0]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h0, h2136, h2141, h2143, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h0, h2136, h2145, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h2139, hlam, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h1902, hlam, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h2136, hlam, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [hlam, p2182_0]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h1902, h2145, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h2143, hlam, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h1904, hlam, p2182_0]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h2138, hlam, p2182_0]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h2142, hlam, p2182_0]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [hlam, p2182_0]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h2145, hlam, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, p2182_1, u1ehi4]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p2182_1, u1ehi4]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h2142, h2145, hc34, hc45, hlam, hphi, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [h2145, hc34, hc45, hlam, hphi, p2182_1]
                                        · have p2182_0 := h2182c.1
                                          have p2182_1 := h2182c.2.1
                                          have p2182_2 := h2182c.2.2.1
                                          have p2182_3 := h2182c.2.2.2
                                          linarith only [hlam, p2182_0]
                                  · linarith only [h2142, h2177, hlam]
                                · linarith only [h2176, hlam, p2147_0]
                              · linarith only [h1904, h2175, hlam]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h1, h2134, hc23, hlam, hphi, ht12, p2147_1, u1ehi1]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h2134, hc23, hlam, hphi, ht12, p2147_1, u1ehi1]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              rcases p2147_3 (m.d 0 3) (by simp) with h2214 | h2214
                              · linarith only [h2214, h4, hlam]
                              · linarith only [h1903, h2214, hlam]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              rcases p2147_3 (m.d 0 3) (by simp) with h2217 | h2217
                              · linarith only [h2217, h4, hlam]
                              · linarith only [h1904, h2217, hlam]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h1903, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h2137, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h2141, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h2145, hlam, p2147_1]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h1904, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h2138, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h2142, hlam, p2147_0]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [h1902, h2142, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2147_1]
                            · have p2147_0 := h2147c.1
                              have p2147_1 := h2147c.2.1
                              have p2147_2 := h2147c.2.2.1
                              have p2147_3 := h2147c.2.2.2
                              linarith only [hlam, p2147_0]
                      · linarith only [h0, h2136, h2138, h2139, h2142, h4, hc13, hlam, hphi, u1ehi3]
                    · linarith only [h0, h2136, h2139, h2141, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · linarith only [h1904, h2138, h4, hc23, hlam, hphi, ht12, u1ehi2]
              · linarith only [h1902, h1903, h1905, h2134, h2136, h2137, h4, hc23, hlam, hphi, ht12, u1ehi4]
            · linarith only [h1902, h2136, h4, hc12, hc23, hlam, hphi]
      · linarith only [h1902, h1904, h4, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2236 | h2236
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2237 | h2237
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2238 | h2238
          · linarith only [h1902, h2238, h3, h4, hc12, hlam, hphi, u1ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2240 | h2240
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2241 | h2241
              · linarith only [h1902, h1903, h2241, h3, h4, hc13, hlam, hphi, u1ehi4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2243 | h2243
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2244 | h2244
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2245 | h2245
                    · linarith only [h1902, h1903, h2245, h3, h4, hc23, hlam, hphi, ht12, u1ehi4]
                    · linarith only [h1902, h2245, h3, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                  · linarith only [h1903, h2237, h2241, h2244, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                · linarith only [h2236, h2238, h2240, h2243, h4, hc23, hlam, hphi, ht12, u1ehi4]
            · linarith only [h1902, h2240, h4, hc12, hc23, hlam, hphi]
        · linarith only [h1902, h1903, h2237, h4, hlam]
      · linarith only [h1902, h2236, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2253 | h2253
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2254 | h2254
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2255 | h2255
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2256 | h2256
          · linarith only [h0, h2256, h4, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2258 | h2258
            · linarith only [h0, h1902, h2258, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2260 | h2260
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2261 | h2261
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2262 | h2262
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2263 | h2263
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2264 | h2264
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2265 | h2265
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2266 | h2266
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
                              linarith only [h2260, h2266, hc03, hc45, hlam, hphi, ht0b, ht5b, p2267_1]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h4, hlam, p2267_1]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              rcases p2267_3 (m.d 0 3) (by simp) with h2271 | h2271
                              · rcases p2267_3 (m.d 1 3) (by simp) with h2272 | h2272
                                · linarith only [h1, h2272, hlam]
                                · linarith only [h2260, h2272, hlam]
                              · linarith only [h2271, hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              rcases p2267_3 (m.d 0 3) (by simp) with h2276 | h2276
                              · rcases p2267_3 (m.d 1 3) (by simp) with h2277 | h2277
                                · linarith only [h1, h2277, hlam]
                                · linarith only [h2261, h2277, hlam]
                              · linarith only [h2276, hlam, p2267_0]
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
                              linarith only [h2256, hlam, p2267_1]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h1, h2266, hc01, hc45, hlam, hphi, ht0b, ht5b, p2267_1]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              rcases p2267_3 (m.d 0 3) (by simp) with h2285 | h2285
                              · rcases p2267_3 (m.d 1 3) (by simp) with h2286 | h2286
                                · rcases p2267_3 (m.d 2 3) (by simp) with h2287 | h2287
                                  · rcases p2267_3 (m.d 3 4) (by simp) with h2288 | h2288
                                    · linarith only [h2260, h2288, hlam]
                                    · linarith only [h2266, h2288, hlam]
                                  · linarith only [h2264, h2287, hlam]
                                · linarith only [h2286, hlam, p2267_0]
                              · linarith only [h2254, h2285, hlam]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h1, hc23, hlam, hphi, ht12, p2267_1, u1ehi2]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h2260, h2262, hc23, hlam, hphi, ht12, p2267_1, u1ehi4]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              rcases p2267_3 (m.d 0 3) (by simp) with h2297 | h2297
                              · linarith only [h2297, h4, hlam]
                              · linarith only [h2253, h2297, hlam]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              rcases p2267_3 (m.d 0 3) (by simp) with h2300 | h2300
                              · linarith only [h2300, h4, hlam]
                              · linarith only [h2254, h2300, hlam]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h2253, hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h2260, hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h2263, hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h1, h2260, hc01, hc35, hlam, hphi, ht0b, ht5b, p2267_1]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h2254, hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h2261, hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h2264, hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [h2266, hlam, p2267_0]
                            · have p2267_0 := h2267c.1
                              have p2267_1 := h2267c.2.1
                              have p2267_2 := h2267c.2.2.1
                              have p2267_3 := h2267c.2.2.2
                              linarith only [hlam, p2267_0]
                          · rcases h3bigk with h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h4, hc23, hlam, hphi, ht12, p2313_1, u1ehi2]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h4, hlam, p2313_1]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              rcases p2313_3 (m.d 0 3) (by simp) with h2317 | h2317
                              · rcases p2313_3 (m.d 1 3) (by simp) with h2318 | h2318
                                · linarith only [h1, h2318, hlam]
                                · linarith only [h2260, h2318, hlam]
                              · linarith only [h2317, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              rcases p2313_3 (m.d 0 3) (by simp) with h2322 | h2322
                              · rcases p2313_3 (m.d 1 3) (by simp) with h2323 | h2323
                                · linarith only [h1, h2323, hlam]
                                · linarith only [h2261, h2323, hlam]
                              · linarith only [h2322, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h1, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2256, hlam, p2313_1]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              rcases p2313_3 (m.d 0 3) (by simp) with h2330 | h2330
                              · rcases p2313_3 (m.d 1 3) (by simp) with h2331 | h2331
                                · rcases p2313_3 (m.d 2 3) (by simp) with h2332 | h2332
                                  · rcases p2313_3 (m.d 3 4) (by simp) with h2333 | h2333
                                    · linarith only [h2333, hlam, p2313_0]
                                    · rcases p2313_3 (m.d 3 5) (by simp) with h2335 | h2335
                                      · linarith only [h2261, h2335, hlam]
                                      · linarith only [h2266, h2335, hlam]
                                  · linarith only [h2263, h2332, hlam]
                                · linarith only [h2331, hlam, p2313_0]
                              · linarith only [h2253, h2330, hlam]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              rcases p2313_3 (m.d 0 3) (by simp) with h2341 | h2341
                              · rcases p2313_3 (m.d 1 3) (by simp) with h2342 | h2342
                                · rcases p2313_3 (m.d 2 3) (by simp) with h2343 | h2343
                                  · rcases p2313_3 (m.d 3 4) (by simp) with h2344 | h2344
                                    · linarith only [h2260, h2344, hlam]
                                    · rcases p2313_3 (m.d 3 5) (by simp) with h2346 | h2346
                                      · linarith only [h2346, hlam, p2313_0]
                                      · rcases h5bigk with h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2258, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2348_1, u1ehi1]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h1902, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          rcases p2348_3 (m.d 0 5) (by simp) with h2352 | h2352
                                          · rcases p2348_3 (m.d 1 5) (by simp) with h2353 | h2353
                                            · linarith only [h2353, h3, hlam]
                                            · linarith only [h2261, h2353, hlam]
                                          · linarith only [h2254, h2352, hlam]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h1902, h2263, h2265, h2266, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2348_1]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h3, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2258, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2266, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2348_1]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h1, h2260, h2262, h2266, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2348_1]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2263, h2265, h3, hc23, hlam, hphi, ht12, p2348_1, u1ehi4]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2263, h2265, hc23, hlam, hphi, ht12, p2348_1, u1ehi4]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          rcases p2348_3 (m.d 0 5) (by simp) with h2366 | h2366
                                          · linarith only [h1902, h2366, hlam]
                                          · linarith only [h2254, h2366, hlam]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2263, h2265, h2266, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2348_1]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2254, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2261, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2264, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2266, hlam, p2348_1]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2255, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2262, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2265, hlam, p2348_0]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [h2266, hc34, hc45, hlam, hphi, p2348_1]
                                        · have p2348_0 := h2348c.1
                                          have p2348_1 := h2348c.2.1
                                          have p2348_2 := h2348c.2.2.1
                                          have p2348_3 := h2348c.2.2.2
                                          linarith only [hlam, p2348_0]
                                  · linarith only [h2264, h2343, hlam]
                                · linarith only [h2342, hlam, p2313_0]
                              · linarith only [h2254, h2341, hlam]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h1, hc23, hlam, hphi, ht12, p2313_1, u1ehi2]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2260, hc23, hlam, hphi, ht12, p2313_1, u1ehi3]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              rcases p2313_3 (m.d 0 3) (by simp) with h2386 | h2386
                              · linarith only [h2386, h4, hlam]
                              · linarith only [h2253, h2386, hlam]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              rcases p2313_3 (m.d 0 3) (by simp) with h2389 | h2389
                              · linarith only [h2389, h4, hlam]
                              · linarith only [h2254, h2389, hlam]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2253, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2260, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2263, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2266, hlam, p2313_1]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2254, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2261, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h2264, hlam, p2313_0]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [h1, h2261, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2313_1]
                            · have p2313_0 := h2313c.1
                              have p2313_1 := h2313c.2.1
                              have p2313_2 := h2313c.2.2.1
                              have p2313_3 := h2313c.2.2.2
                              linarith only [hlam, p2313_0]
                        · linarith only [h0, h1, h1902, h2260, h2262, h2265, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                      · linarith only [h0, h2261, h2264, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · linarith only [h0, h2263, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h2253, h2255, h2262, h4, hc23, hlam, hphi, ht12, u1ehi3]
                · linarith only [h2254, h2261, h4, hc23, hlam, hphi, ht12, u1ehi2]
              · linarith only [h2253, h2256, h2260, h4, hc23, hlam, hphi, ht12, u1ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2408 | h2408
          · linarith only [h0, h2408, h4, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2410 | h2410
            · linarith only [h0, h1902, h2410, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2412 | h2412
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2413 | h2413
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2414 | h2414
                  · linarith only [h2, h2255, h2414, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2416 | h2416
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2417 | h2417
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2418 | h2418
                        · linarith only [h2, h2255, h2418, hc24, hlam, hphi, ht12, u1ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2420 | h2420
                          · linarith only [h0, h1902, h2412, h2418, h2420, hc13, hlam, hphi, u1ehi1]
                          · rcases h3bigk with h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c | h2422c
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h4, hc23, hlam, hphi, ht12, p2422_1, u1ehi2]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h4, hlam, p2422_1]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              rcases p2422_3 (m.d 0 3) (by simp) with h2426 | h2426
                              · rcases p2422_3 (m.d 1 3) (by simp) with h2427 | h2427
                                · linarith only [h1, h2427, hlam]
                                · linarith only [h2412, h2427, hlam]
                              · linarith only [h2426, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              rcases p2422_3 (m.d 0 3) (by simp) with h2431 | h2431
                              · rcases p2422_3 (m.d 1 3) (by simp) with h2432 | h2432
                                · linarith only [h1, h2432, hlam]
                                · linarith only [h2413, h2432, hlam]
                              · linarith only [h2431, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h1, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h2408, hlam, p2422_1]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              rcases p2422_3 (m.d 0 3) (by simp) with h2439 | h2439
                              · rcases p2422_3 (m.d 1 3) (by simp) with h2440 | h2440
                                · rcases p2422_3 (m.d 2 3) (by simp) with h2441 | h2441
                                  · rcases p2422_3 (m.d 3 4) (by simp) with h2442 | h2442
                                    · linarith only [h2442, hlam, p2422_0]
                                    · rcases p2422_3 (m.d 3 5) (by simp) with h2444 | h2444
                                      · linarith only [h2413, h2444, hlam]
                                      · linarith only [h2420, h2444, hlam]
                                  · linarith only [h2416, h2441, hlam]
                                · linarith only [h2440, hlam, p2422_0]
                              · linarith only [h2253, h2439, hlam]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              rcases p2422_3 (m.d 0 3) (by simp) with h2450 | h2450
                              · rcases p2422_3 (m.d 1 3) (by simp) with h2451 | h2451
                                · rcases p2422_3 (m.d 2 3) (by simp) with h2452 | h2452
                                  · rcases p2422_3 (m.d 3 4) (by simp) with h2453 | h2453
                                    · linarith only [h2412, h2453, hlam]
                                    · rcases p2422_3 (m.d 3 5) (by simp) with h2455 | h2455
                                      · linarith only [h2455, hlam, p2422_0]
                                      · rcases h5bigk with h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c | h2457c
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2414, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2457_1, u1ehi3]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h1902, hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h1902, h2418, h2420, hc34, hc45, hlam, hphi, p2457_1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2255, hlam, p2457_1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h3, hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2410, hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2420, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2457_1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2414, hlam, p2457_1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2418, h3, hc45, hlam, hphi, ht12, ht23, ht34, p2457_1, u1ehi4]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2418, hc45, hlam, hphi, ht12, ht23, ht34, p2457_1, u1ehi4]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2418, h2420, hc34, hc45, hlam, hphi, p2457_1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2418, hlam, p2457_1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2254, hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2413, hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2417, hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [hlam, p2457_0]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2420, hlam, p2457_1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h0, h1902, hc45, hlam, hphi, ht12, ht23, ht34, p2457_1, u1ehi1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2410, hc45, hlam, hphi, ht12, ht23, ht34, p2457_1, u1ehi1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h0, h1902, hc45, hlam, hphi, ht12, ht23, ht34, p2457_1, u1ehi1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [h2420, hc34, hc45, hlam, hphi, p2457_1]
                                        · have p2457_0 := h2457c.1
                                          have p2457_1 := h2457c.2.1
                                          have p2457_2 := h2457c.2.2.1
                                          have p2457_3 := h2457c.2.2.2
                                          linarith only [hlam, p2457_0]
                                  · linarith only [h2417, h2452, hlam]
                                · linarith only [h2451, hlam, p2422_0]
                              · linarith only [h2254, h2450, hlam]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h1, hc23, hlam, hphi, ht12, p2422_1, u1ehi2]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [hc23, hlam, hphi, ht12, p2422_1, u1ehi2]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              rcases p2422_3 (m.d 0 3) (by simp) with h2489 | h2489
                              · linarith only [h2489, h4, hlam]
                              · linarith only [h2253, h2489, hlam]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              rcases p2422_3 (m.d 0 3) (by simp) with h2492 | h2492
                              · linarith only [h2492, h4, hlam]
                              · linarith only [h2254, h2492, hlam]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h2253, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h2412, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h2416, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h2420, hlam, p2422_1]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h2254, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h2413, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h2417, hlam, p2422_0]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [h1, h2413, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2422_1]
                            · have p2422_0 := h2422c.1
                              have p2422_1 := h2422c.2.1
                              have p2422_2 := h2422c.2.2.1
                              have p2422_3 := h2422c.2.2.2
                              linarith only [hlam, p2422_0]
                      · linarith only [h1, h2413, h2417, h4, hlam]
                    · linarith only [h0, h2416, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h2254, h2413, h4, hc23, hlam, hphi, ht12, u1ehi2]
              · linarith only [h2253, h2408, h2412, h4, hc23, hlam, hphi, ht12, u1ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2509 | h2509
        · linarith only [h2253, h2254, h2509, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2511 | h2511
          · linarith only [h0, h2511, h4, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2513 | h2513
            · linarith only [h0, h1902, h2513, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2515 | h2515
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2516 | h2516
                · linarith only [h1, h2254, h2516, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2518 | h2518
                  · linarith only [h2, h2509, h2518, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2520 | h2520
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2521 | h2521
                      · linarith only [h2, h2253, h2254, h2521, hc23, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h0, h2521, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h0, h2520, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h2253, h2511, h2515, h4, hc23, hlam, hphi, ht12, u1ehi1]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2526 | h2526
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2527 | h2527
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2528 | h2528
          · linarith only [h0, h2528, h4, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2530 | h2530
            · linarith only [h0, h1902, h2530, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2532 | h2532
              · linarith only [h1, h2253, h2526, h2532, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2534 | h2534
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2535 | h2535
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2536 | h2536
                    · linarith only [h0, h1902, h2253, h2526, h2536, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h0, h2536, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h2253, h2527, h2530, h2532, h2534, h2535, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h2526, h2534, h4, hc23, hlam, hphi, ht12, u1ehi2]
        · linarith only [h2253, h2526, h2527, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2542 | h2542
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2543 | h2543
          · linarith only [h0, h2543, h4, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2545 | h2545
            · linarith only [h0, h1902, h2545, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2547 | h2547
              · linarith only [h0, h2253, h2547, h4, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2549 | h2549
                · linarith only [h1, h2526, h2549, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2551 | h2551
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2552 | h2552
                    · linarith only [h0, h2253, h2552, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h0, h2552, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h2253, h2542, h2551, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2556 | h2556
          · linarith only [h0, h2556, h4, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2558 | h2558
            · linarith only [h0, h1902, h2558, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2560 | h2560
              · linarith only [h1, h2253, h2560, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2562 | h2562
                · linarith only [h1, h2526, h2562, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2564 | h2564
                  · linarith only [h0, h2253, h2542, h2564, h4, hc14, hlam, hphi, u1ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2566 | h2566
                    · linarith only [h0, h2253, h2566, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h0, h2566, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 5134000 in
set_option maxHeartbeats 5134000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s2 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3 m hb1 hb3 hb5 h0 h1 h2 h3
  · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5138000 in
set_option maxHeartbeats 5138000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_R_L_I_H_I_s2 m hb1 hb3 hb5 h0 h1 h2
  · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5142000 in
set_option maxHeartbeats 5142000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_R_L_I_H_I_s1 m hb1 hb3 hb5 h0 h1
  · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

end R2N4
