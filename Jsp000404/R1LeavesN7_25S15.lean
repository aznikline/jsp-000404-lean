import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S13
import Jsp000404.R1LeavesN7_25S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1668 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1848 | h1848
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1849 | h1849
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1850 | h1850
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1851 | h1851
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1852 | h1852
          · linarith only [h0, h1852, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1854 | h1854
            · linarith only [h0, h1668, h1854, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1856 | h1856
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1857 | h1857
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1858 | h1858
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1859 | h1859
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1860 | h1860
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1861 | h1861
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1862 | h1862
                          · rcases h0bigk with h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1848, h1860, h1862, hc01, hc45, hlam, hphi, ht0b, ht5b, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1, h1857, h1862, hc01, hc45, hlam, hphi, ht0b, ht5b, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1668, h1848, h1860, h1862, hc01, hc45, hlam, hphi, ht0b, ht5b, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              rcases p1863_3 (m.d 0 1) (by simp) with h1868 | h1868
                              · rcases p1863_3 (m.d 0 2) (by simp) with h1869 | h1869
                                · linarith only [h0, h1869, hlam]
                                · linarith only [h1848, h1869, hlam]
                              · linarith only [h1868, h3, hlam]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h0, hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h4, hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1668, hlam, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1668, h1859, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1, hlam, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h0, h1668, h1856, h1860, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              rcases p1863_3 (m.d 0 1) (by simp) with h1882 | h1882
                              · rcases p1863_3 (m.d 0 2) (by simp) with h1883 | h1883
                                · linarith only [h1883, h4, hlam]
                                · linarith only [h1848, h1883, hlam]
                              · linarith only [h1882, h3, hlam]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h2, hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h0, h1856, h1860, h1862, hc04, hc45, hlam, hphi, ht0b, ht5b, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1849, hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              rcases p1863_3 (m.d 0 1) (by simp) with h1891 | h1891
                              · rcases p1863_3 (m.d 0 2) (by simp) with h1892 | h1892
                                · linarith only [h1668, h1892, hlam]
                                · linarith only [h1848, h1892, hlam]
                              · linarith only [h1891, h3, hlam]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h3, hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1848, hlam, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1850, hlam, p1863_0]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [h1851, hlam, p1863_1]
                            · have p1863_0 := h1863c.1
                              have p1863_1 := h1863c.2.1
                              have p1863_2 := h1863c.2.2.1
                              have p1863_3 := h1863c.2.2.2
                              linarith only [hlam, p1863_0]
                          · rcases h0bigk with h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h0, h1856, hc01, hc25, hlam, hphi, ht0b, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h0, h1856, h1861, h1862, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h0, h1668, h1856, h1861, h1862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1848, h1861, h1862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h0, hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h4, hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1668, hlam, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1668, h1859, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1, hlam, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h0, h1856, h1861, h1862, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h0, h1668, h1856, h1861, h1862, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1848, h1861, h1862, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h2, hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h0, h1856, h1861, h1862, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1849, hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1848, h1861, h1862, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h3, hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1848, hlam, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1850, hlam, p1901_0]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [h1851, hlam, p1901_1]
                            · have p1901_0 := h1901c.1
                              have p1901_1 := h1901c.2.1
                              have p1901_2 := h1901c.2.2.1
                              have p1901_3 := h1901c.2.2.2
                              linarith only [hlam, p1901_0]
                        · linarith only [h1668, h1861, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1856, h1860, h4, hc25, hlam, hphi, u5elo3]
                    · linarith only [h1849, h1859, h4, hlam]
                  · linarith only [h1851, h1854, h1856, h1858, hc25, hlam, hphi, u5elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1931 | h1931
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1932 | h1932
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1933 | h1933
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1934 | h1934
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1935 | h1935
                          · rcases h0bigk with h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h0, h1856, h1933, h1935, hc01, hc45, hlam, hphi, ht0b, ht5b, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h1849, h1857, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h0, h1668, h1856, h1933, h1935, hc01, hc45, hlam, hphi, ht0b, ht5b, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              rcases p1936_3 (m.d 0 1) (by simp) with h1941 | h1941
                              · rcases p1936_3 (m.d 0 2) (by simp) with h1942 | h1942
                                · linarith only [h0, h1942, hlam]
                                · linarith only [h1848, h1942, hlam]
                              · linarith only [h1941, h3, hlam]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h0, hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h4, hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h1668, hlam, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h1, hlam, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h0, h1856, h1933, h1935, hc03, hc45, hlam, hphi, ht0b, ht5b, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h1849, h1852, h1856, h1857, h1933, h1935, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              rcases p1936_3 (m.d 0 1) (by simp) with h1955 | h1955
                              · rcases p1936_3 (m.d 0 2) (by simp) with h1956 | h1956
                                · linarith only [h1956, h4, hlam]
                                · linarith only [h1848, h1956, hlam]
                              · linarith only [h1955, h3, hlam]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h2, hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h0, h1856, h1933, h1935, hc04, hc45, hlam, hphi, ht0b, ht5b, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h1849, hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              rcases p1936_3 (m.d 0 1) (by simp) with h1964 | h1964
                              · rcases p1936_3 (m.d 0 2) (by simp) with h1965 | h1965
                                · linarith only [h1668, h1965, hlam]
                                · linarith only [h1848, h1965, hlam]
                              · linarith only [h1964, h3, hlam]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h3, hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h1848, hlam, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h1850, hlam, p1936_0]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [h1851, hlam, p1936_1]
                            · have p1936_0 := h1936c.1
                              have p1936_1 := h1936c.2.1
                              have p1936_2 := h1936c.2.2.1
                              have p1936_3 := h1936c.2.2.2
                              linarith only [hlam, p1936_0]
                          · linarith only [h1852, h1856, h1857, h1933, h1935, hc35, hlam, hphi, u5elo4]
                        · linarith only [h0, h1668, h1856, h1933, h1934, hc35, hlam, hphi, u5elo4]
                      · linarith only [h1, h1852, h1856, h1933, h4, hc25, hlam, hphi, u5elo3]
                    · linarith only [h1849, h1932, h4, hlam]
                  · linarith only [h1852, h1856, h1857, h1931, hc25, hlam, hphi, u5elo4]
              · linarith only [h1668, h1848, h1856, hc12, hc24, hlam, hphi]
        · linarith only [h1668, h1848, h1851, hc25, hlam, hphi, u5elo4]
      · linarith only [h1849, h1850, hc34, hlam, hphi, ht45, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1982 | h1982
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1983 | h1983
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1984 | h1984
          · linarith only [h0, h1848, h1984, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1986 | h1986
            · linarith only [h0, h1668, h1986, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1988 | h1988
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1989 | h1989
                · linarith only [h1, h1849, h1989, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1991 | h1991
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1992 | h1992
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1993 | h1993
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1994 | h1994
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1995 | h1995
                          · rcases h0bigk with h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h0, h1988, h1993, h1995, hc01, hc45, hlam, hphi, ht0b, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1, h1984, h1988, h1993, h1995, hc01, hc45, hlam, hphi, ht0b, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1984, h1988, h1989, h1993, h1995, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              rcases p1996_3 (m.d 0 1) (by simp) with h2001 | h2001
                              · rcases p1996_3 (m.d 0 2) (by simp) with h2002 | h2002
                                · linarith only [h0, h2002, hlam]
                                · linarith only [h1848, h2002, hlam]
                              · linarith only [h2001, h3, hlam]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h0, hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h4, hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1668, hlam, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1, hlam, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h0, h1988, h1993, h1995, hc03, hc45, hlam, hphi, ht0b, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1849, hlam, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1849, h1988, h1992, h1993, h1995, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h2, hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h0, h1988, h1993, h1995, hc04, hc45, hlam, hphi, ht0b, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1849, h1992, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1849, h1988, h1992, h1993, h1995, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h3, hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1848, hlam, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1982, hlam, p1996_0]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [h1983, hlam, p1996_1]
                            · have p1996_0 := h1996c.1
                              have p1996_1 := h1996c.2.1
                              have p1996_2 := h1996c.2.2.1
                              have p1996_3 := h1996c.2.2.2
                              linarith only [hlam, p1996_0]
                          · linarith only [h1849, h1984, h1988, h1989, h1993, h1995, h2, hc35, hlam, hphi, u5elo4]
                        · linarith only [h0, h1668, h1988, h1991, h1993, h1994, h3, hc35, hlam, hphi, u5elo0]
                      · linarith only [h1993, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2029 | h2029
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2030 | h2030
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2031 | h2031
                          · rcases h0bigk with h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h0, h1988, h2029, h2031, hc01, hc45, hlam, hphi, ht0b, ht5b, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h0, h1988, h2029, h2031, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h0, h1668, h1988, h2029, h2031, hc01, hc45, hlam, hphi, ht0b, ht5b, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              rcases p2032_3 (m.d 0 1) (by simp) with h2037 | h2037
                              · rcases p2032_3 (m.d 0 2) (by simp) with h2038 | h2038
                                · linarith only [h0, h2038, hlam]
                                · linarith only [h1848, h2038, hlam]
                              · linarith only [h2037, h3, hlam]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h0, hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h4, hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1668, hlam, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1992, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1, hlam, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h0, h1849, h1988, hc04, hc25, hlam, hphi, ht0b, ht5b, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1849, hlam, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1848, h1992, h2029, h2031, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h2, hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1668, h1992, hc02, hc34, hlam, hphi, ht23, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1668, h1992, hc03, hc34, hlam, hphi, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              rcases p2032_3 (m.d 0 1) (by simp) with h2056 | h2056
                              · rcases p2032_3 (m.d 0 2) (by simp) with h2057 | h2057
                                · linarith only [h1668, h2057, hlam]
                                · linarith only [h1848, h2057, hlam]
                              · linarith only [h2056, h3, hlam]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h3, hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1848, hlam, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1982, hlam, p2032_0]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [h1983, hlam, p2032_1]
                            · have p2032_0 := h2032c.1
                              have p2032_1 := h2032c.2.1
                              have p2032_2 := h2032c.2.2.1
                              have p2032_3 := h2032c.2.2.2
                              linarith only [hlam, p2032_0]
                          · linarith only [h1992, h2031, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h1668, h1848, h1991, h2030, h3, hlam]
                      · linarith only [h2029, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1983, h1986, h1988, h1991, hc25, hlam, hphi, u5elo0]
              · linarith only [h1848, h1988, h4, hc12, hc23, hlam, hphi]
        · linarith only [h1668, h1848, h1983, hc25, hlam, hphi, u5elo4]
      · linarith only [h1848, h1982, h4, hc25, hlam, hphi, u5elo3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2073 | h2073
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2074 | h2074
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2075 | h2075
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2076 | h2076
          · linarith only [h0, h2076, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2078 | h2078
            · linarith only [h0, h1668, h2078, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2080 | h2080
              · linarith only [h0, h1848, h2080, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2082 | h2082
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2083 | h2083
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2084 | h2084
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2085 | h2085
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2086 | h2086
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2087 | h2087
                          · rcases h0bigk with h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              rcases p2088_3 (m.d 0 1) (by simp) with h2090 | h2090
                              · rcases p2088_3 (m.d 0 2) (by simp) with h2091 | h2091
                                · linarith only [h0, h2091, hlam]
                                · rcases p2088_3 (m.d 0 3) (by simp) with h2093 | h2093
                                  · linarith only [h1, h2093, hlam]
                                  · linarith only [h2093, h4, hlam]
                              · linarith only [h0, h2090, hlam]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h1, h2082, h2087, hc01, hc45, hlam, hphi, ht0b, ht5b, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h2, h2082, h2087, hc01, hc45, hlam, hphi, ht0b, ht5b, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              rcases p2088_3 (m.d 0 1) (by simp) with h2099 | h2099
                              · rcases p2088_3 (m.d 0 2) (by simp) with h2100 | h2100
                                · linarith only [h0, h2100, hlam]
                                · rcases p2088_3 (m.d 0 3) (by simp) with h2102 | h2102
                                  · linarith only [h1, h2102, hlam]
                                  · linarith only [h2074, h2102, hlam]
                              · linarith only [h2099, h3, hlam]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h0, hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h4, hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h1668, hlam, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h1848, hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h1, hlam, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h2, h2082, h2087, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h0, h1848, h4, hc12, hc23, hlam, hphi, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h2, hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h0, h1668, hc12, hc24, hlam, hphi, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h2073, hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h0, h1848, h2073, h4, hc12, hc23, hlam, hphi, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h3, hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2088_1, u5elo0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h2074, hlam, p2088_0]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [h2075, hlam, p2088_1]
                            · have p2088_0 := h2088c.1
                              have p2088_1 := h2088c.2.1
                              have p2088_2 := h2088c.2.2.1
                              have p2088_3 := h2088c.2.2.2
                              linarith only [hlam, p2088_0]
                          · rcases h0bigk with h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              rcases p2126_3 (m.d 0 1) (by simp) with h2128 | h2128
                              · rcases p2126_3 (m.d 0 2) (by simp) with h2129 | h2129
                                · linarith only [h0, h2129, hlam]
                                · rcases p2126_3 (m.d 0 3) (by simp) with h2131 | h2131
                                  · linarith only [h1, h2131, hlam]
                                  · linarith only [h2131, h4, hlam]
                              · linarith only [h0, h2128, hlam]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h1, h2082, h2083, h2087, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h2, h2083, h2087, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h2075, h2087, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h0, hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h4, hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h1668, hlam, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h1848, hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h1, hlam, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h2, h2083, h2087, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h0, h1848, h4, hc12, hc23, hlam, hphi, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h2, hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h0, h1668, h2084, hc12, hc23, hlam, hphi, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h2073, hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h0, h1668, h1848, h2084, hc12, hc23, hlam, hphi, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h3, hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2126_1, u5elo0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h2074, hlam, p2126_0]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [h2075, hlam, p2126_1]
                            · have p2126_0 := h2126c.1
                              have p2126_1 := h2126c.2.1
                              have p2126_2 := h2126c.2.2.1
                              have p2126_3 := h2126c.2.2.2
                              linarith only [hlam, p2126_0]
                        · linarith only [h0, h1668, h2086, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1848, h2074, h2085, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h2073, h2084, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2161 | h2161
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2162 | h2162
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2163 | h2163
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2164 | h2164
                          · linarith only [h2082, h2083, h2164, hlam]
                          · rcases h0bigk with h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              rcases p2166_3 (m.d 0 1) (by simp) with h2168 | h2168
                              · rcases p2166_3 (m.d 0 2) (by simp) with h2169 | h2169
                                · linarith only [h0, h2169, hlam]
                                · rcases p2166_3 (m.d 0 3) (by simp) with h2171 | h2171
                                  · linarith only [h1, h2171, hlam]
                                  · linarith only [h2171, h4, hlam]
                              · linarith only [h0, h2168, hlam]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h2073, h2075, h2078, h2083, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h2075, h2078, h2083, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h2075, h2078, h2083, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h0, hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h4, hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h1668, hlam, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h1848, hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h1, hlam, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h2075, h2078, h2083, h4, hc12, hc23, hlam, hphi, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h0, h1848, h4, hc12, hc23, hlam, hphi, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h2, hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h0, h1668, hc12, hc24, hlam, hphi, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h2073, hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h0, h1848, h2073, h4, hc12, hc23, hlam, hphi, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h3, hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2166_1, u5elo0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h2074, hlam, p2166_0]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [h2075, hlam, p2166_1]
                            · have p2166_0 := h2166c.1
                              have p2166_1 := h2166c.2.1
                              have p2166_2 := h2166c.2.2.1
                              have p2166_3 := h2166c.2.2.2
                              linarith only [hlam, p2166_0]
                        · linarith only [h0, h1668, h2163, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1848, h2074, h2162, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h2073, h2075, h2082, h2083, h2161, h4, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2201 | h2201
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2202 | h2202
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2203 | h2203
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2204 | h2204
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2205 | h2205
                          · rcases h0bigk with h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              rcases p2206_3 (m.d 0 1) (by simp) with h2208 | h2208
                              · rcases p2206_3 (m.d 0 2) (by simp) with h2209 | h2209
                                · linarith only [h0, h2209, hlam]
                                · rcases p2206_3 (m.d 0 3) (by simp) with h2211 | h2211
                                  · linarith only [h1, h2211, hlam]
                                  · linarith only [h2211, h4, hlam]
                              · linarith only [h0, h2208, hlam]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2073, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2, h2201, hc01, hc45, hlam, hphi, ht0b, ht5b, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              rcases p2206_3 (m.d 0 1) (by simp) with h2217 | h2217
                              · rcases p2206_3 (m.d 0 2) (by simp) with h2218 | h2218
                                · linarith only [h0, h2218, hlam]
                                · rcases p2206_3 (m.d 0 3) (by simp) with h2220 | h2220
                                  · linarith only [h1, h2220, hlam]
                                  · linarith only [h2074, h2220, hlam]
                              · linarith only [h2217, h3, hlam]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h0, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h4, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h1668, hlam, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h1848, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h1, hlam, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2073, h2076, h2082, h4, hc12, hc23, hlam, hphi, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h0, h1848, h4, hc12, hc23, hlam, hphi, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h0, h1668, hc12, hc24, hlam, hphi, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2073, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h0, h1848, h2073, h4, hc12, hc23, hlam, hphi, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h3, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2206_1, u5elo0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2074, hlam, p2206_0]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [h2075, hlam, p2206_1]
                            · have p2206_0 := h2206c.1
                              have p2206_1 := h2206c.2.1
                              have p2206_2 := h2206c.2.2.1
                              have p2206_3 := h2206c.2.2.2
                              linarith only [hlam, p2206_0]
                          · linarith only [h2076, h2082, h2205, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1668, h2073, h2082, h2201, h2204, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h1848, h2073, h2074, h2082, h2203, h4, hc14, hlam, hphi, ht45, u5elo2]
                    · linarith only [h2073, h2202, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2248 | h2248
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2249 | h2249
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2250 | h2250
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2251 | h2251
                          · linarith only [h2073, h2076, h2082, h2201, h2251, h4, hc12, hc23, hlam, hphi]
                          · linarith only [h1848, h2075, h2076, h2082, h2251, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1668, h1848, h2075, h2250, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1848, h2074, h2249, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h2073, h2075, h2076, h2082, h2201, h2248, h4, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2257 | h2257
          · linarith only [h0, h2257, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2259 | h2259
            · linarith only [h0, h1668, h2259, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2261 | h2261
              · linarith only [h0, h1668, h1848, h2075, h2261, hc05, hlam, hphi, u5elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2263 | h2263
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2264 | h2264
                  · linarith only [h2, h2075, h2264, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2266 | h2266
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2267 | h2267
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2268 | h2268
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2269 | h2269
                          · linarith only [h1, h2075, h2263, h2269, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h0bigk with h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              rcases p2271_3 (m.d 0 1) (by simp) with h2273 | h2273
                              · rcases p2271_3 (m.d 0 2) (by simp) with h2274 | h2274
                                · linarith only [h0, h2274, hlam]
                                · rcases p2271_3 (m.d 0 3) (by simp) with h2276 | h2276
                                  · linarith only [h1, h2276, hlam]
                                  · linarith only [h2276, h4, hlam]
                              · linarith only [h0, h2273, hlam]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h2073, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2271_1]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              rcases p2271_3 (m.d 0 1) (by simp) with h2281 | h2281
                              · rcases p2271_3 (m.d 0 2) (by simp) with h2282 | h2282
                                · linarith only [h0, h2282, hlam]
                                · rcases p2271_3 (m.d 0 3) (by simp) with h2284 | h2284
                                  · linarith only [h1, h2284, hlam]
                                  · linarith only [h2073, h2284, hlam]
                              · linarith only [h2, h2281, hlam]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              rcases p2271_3 (m.d 0 1) (by simp) with h2288 | h2288
                              · rcases p2271_3 (m.d 0 2) (by simp) with h2289 | h2289
                                · linarith only [h0, h2289, hlam]
                                · rcases p2271_3 (m.d 0 3) (by simp) with h2291 | h2291
                                  · linarith only [h1, h2291, hlam]
                                  · linarith only [h2074, h2291, hlam]
                              · linarith only [h2288, h3, hlam]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h0, hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h4, hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h1668, hlam, p2271_1]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h1848, hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h1, hlam, p2271_1]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p2271_1]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h0, h1668, h4, hc12, hc23, hlam, hphi, p2271_1]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h0, h1848, h4, hc12, hc23, hlam, hphi, p2271_1]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h2, hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h0, h2075, h2268, hc12, hc24, hlam, hphi, p2271_1]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h2073, hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h2075, hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h3, hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2271_1, u5elo0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h2074, hlam, p2271_0]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [h1848, hc04, hlam, hphi, ht45, p2271_1, u5elo2]
                            · have p2271_0 := h2271c.1
                              have p2271_1 := h2271c.2.1
                              have p2271_2 := h2271c.2.2.1
                              have p2271_3 := h2271c.2.2.2
                              linarith only [hlam, p2271_0]
                        · linarith only [h0, h1668, h2268, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h2267, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h2073, h2266, h4, hlam]
                · linarith only [h2073, h2075, h2263, hc13, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h2073, h2074, hc34, hlam, hphi, ht45, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2320 | h2320
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2321 | h2321
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2322 | h2322
          · linarith only [h0, h2322, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2324 | h2324
            · linarith only [h0, h1668, h2324, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2326 | h2326
              · linarith only [h0, h1848, h2326, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2328 | h2328
                · linarith only [h1, h2073, h2328, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2330 | h2330
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2331 | h2331
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2332 | h2332
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2333 | h2333
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2334 | h2334
                          · rcases h0bigk with h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              rcases p2335_3 (m.d 0 1) (by simp) with h2337 | h2337
                              · rcases p2335_3 (m.d 0 2) (by simp) with h2338 | h2338
                                · linarith only [h0, h2338, hlam]
                                · rcases p2335_3 (m.d 0 3) (by simp) with h2340 | h2340
                                  · linarith only [h1, h2340, hlam]
                                  · linarith only [h2340, h4, hlam]
                              · linarith only [h0, h2337, hlam]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2320, hc01, hc35, hlam, hphi, ht0b, ht5b, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2073, h2320, h2334, hc01, hc45, hlam, hphi, ht0b, ht5b, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              rcases p2335_3 (m.d 0 1) (by simp) with h2346 | h2346
                              · rcases p2335_3 (m.d 0 2) (by simp) with h2347 | h2347
                                · linarith only [h0, h2347, hlam]
                                · rcases p2335_3 (m.d 0 3) (by simp) with h2349 | h2349
                                  · linarith only [h1, h2349, hlam]
                                  · linarith only [h2320, h2349, hlam]
                              · linarith only [h2346, h3, hlam]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h0, hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h4, hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h1668, hlam, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h1848, hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h1, hlam, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2073, h2331, hc02, hc23, hlam, hphi, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2073, hlam, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2073, h2331, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2, hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h0, h1668, hc12, hc24, hlam, hphi, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2073, h2331, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2073, h2326, h2331, h3, hc12, hc23, hlam, hphi, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h3, hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2335_1, u5elo0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2320, hlam, p2335_0]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [h2321, hlam, p2335_1]
                            · have p2335_0 := h2335c.1
                              have p2335_1 := h2335c.2.1
                              have p2335_2 := h2335c.2.2.1
                              have p2335_3 := h2335c.2.2.2
                              linarith only [hlam, p2335_0]
                          · linarith only [h2073, h2320, h2330, h2334, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h1668, h2, h2330, h2333, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h2073, h2331, h2332, hc04, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2376 | h2376
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2377 | h2377
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2378 | h2378
                          · rcases h0bigk with h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              rcases p2379_3 (m.d 0 1) (by simp) with h2381 | h2381
                              · rcases p2379_3 (m.d 0 2) (by simp) with h2382 | h2382
                                · linarith only [h0, h2382, hlam]
                                · rcases p2379_3 (m.d 0 3) (by simp) with h2384 | h2384
                                  · linarith only [h1, h2384, hlam]
                                  · linarith only [h2384, h4, hlam]
                              · linarith only [h0, h2381, hlam]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2320, hc01, hc35, hlam, hphi, ht0b, ht5b, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2073, h2320, hc01, hc35, hlam, hphi, ht0b, ht5b, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              rcases p2379_3 (m.d 0 1) (by simp) with h2390 | h2390
                              · rcases p2379_3 (m.d 0 2) (by simp) with h2391 | h2391
                                · linarith only [h0, h2391, hlam]
                                · rcases p2379_3 (m.d 0 3) (by simp) with h2393 | h2393
                                  · linarith only [h1, h2393, hlam]
                                  · linarith only [h2320, h2393, hlam]
                              · linarith only [h2390, h3, hlam]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h0, hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h4, hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h1668, hlam, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h1848, hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h1, hlam, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2073, hlam, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2073, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2, hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h0, h1668, hc12, hc24, hlam, hphi, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2073, hc03, hc34, hlam, hphi, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2073, h2326, h3, hc12, hc34, hlam, hphi, ht23, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h3, hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2379_1, u5elo0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2320, hlam, p2379_0]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [h2321, hlam, p2379_1]
                            · have p2379_0 := h2379c.1
                              have p2379_1 := h2379c.2.1
                              have p2379_2 := h2379c.2.2.1
                              have p2379_3 := h2379c.2.2.2
                              linarith only [hlam, p2379_0]
                          · linarith only [h2331, h2378, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h1668, h2320, h2330, h2331, h2377, h3, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2376, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2420 | h2420
                    · linarith only [h2073, h2320, h2321, h2324, h2330, h2420, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2422 | h2422
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2423 | h2423
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2424 | h2424
                          · linarith only [h2320, h2322, h2328, h2330, h2420, h2424, h4, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1848, h2321, h2420, h2424, h4, hc03, hlam, hphi, ht34, ht45, u5elo2]
                        · linarith only [h1668, h2321, h2423, hlam]
                      · linarith only [h2320, h2321, h2322, h2328, h2330, h2422, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h2073, h2320, h2321, hc35, hlam, hphi, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2430 | h2430
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2431 | h2431
          · linarith only [h0, h1848, h2431, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2433 | h2433
            · linarith only [h0, h1668, h2433, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2435 | h2435
              · linarith only [h0, h2320, h2435, h4, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2437 | h2437
                · linarith only [h1, h2320, h2437, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2439 | h2439
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2440 | h2440
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2441 | h2441
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2442 | h2442
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2443 | h2443
                          · rcases h0bigk with h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              rcases p2444_3 (m.d 0 1) (by simp) with h2446 | h2446
                              · rcases p2444_3 (m.d 0 2) (by simp) with h2447 | h2447
                                · linarith only [h0, h2447, hlam]
                                · rcases p2444_3 (m.d 0 3) (by simp) with h2449 | h2449
                                  · linarith only [h1, h2449, hlam]
                                  · linarith only [h2449, h4, hlam]
                              · linarith only [h0, h2446, hlam]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              rcases p2444_3 (m.d 0 1) (by simp) with h2453 | h2453
                              · rcases p2444_3 (m.d 0 2) (by simp) with h2454 | h2454
                                · linarith only [h0, h2454, hlam]
                                · rcases p2444_3 (m.d 0 3) (by simp) with h2456 | h2456
                                  · linarith only [h1, h2456, hlam]
                                  · rcases p2444_3 (m.d 0 4) (by simp) with h2458 | h2458
                                    · linarith only [h2, h2458, hlam]
                                    · linarith only [h2073, h2458, hlam]
                              · linarith only [h1, h2453, hlam]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h2, h2439, hc01, hc45, hlam, hphi, ht0b, ht5b, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              rcases p2444_3 (m.d 0 1) (by simp) with h2463 | h2463
                              · rcases p2444_3 (m.d 0 2) (by simp) with h2464 | h2464
                                · linarith only [h0, h2464, hlam]
                                · rcases p2444_3 (m.d 0 3) (by simp) with h2466 | h2466
                                  · linarith only [h1, h2466, hlam]
                                  · rcases p2444_3 (m.d 0 4) (by simp) with h2468 | h2468
                                    · linarith only [h2, h2468, hlam]
                                    · linarith only [h2430, h2468, hlam]
                              · linarith only [h2463, h3, hlam]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h0, hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h4, hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h1668, hlam, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h1848, hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h1, hlam, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h0, h2320, h2440, h2443, hc12, hc23, hlam, hphi, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h2073, hlam, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h2320, hlam, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h2, hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h0, h1668, hc12, hc24, hlam, hphi, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h2073, h2440, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h0, h2073, h2320, h2440, h4, hc12, hc23, hlam, hphi, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h3, hlam, p2444_0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2444_1, u5elo0]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h0, h2320, h2441, h4, hc12, hc25, hlam, hphi, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [h2430, hlam, p2444_1]
                            · have p2444_0 := h2444c.1
                              have p2444_1 := h2444c.2.1
                              have p2444_2 := h2444c.2.2.1
                              have p2444_3 := h2444c.2.2.2
                              linarith only [hlam, p2444_0]
                          · linarith only [h2, h2073, h2439, h2443, hlam]
                        · linarith only [h0, h1668, h2, h2073, h2439, h2440, h2442, hc12, hc23, hlam, hphi]
                      · linarith only [h2, h2073, h2439, h2440, h2441, hc45, hlam, hphi, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2495 | h2495
                      · linarith only [h0, h2320, h2440, h2495, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2495, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2498 | h2498
                    · linarith only [h2073, h2430, h2433, h2439, h2498, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2500 | h2500
                      · linarith only [h0, h2320, h2498, h2500, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2500, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2503 | h2503
          · linarith only [h0, h2503, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2505 | h2505
            · linarith only [h0, h1668, h2505, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2507 | h2507
              · linarith only [h0, h1668, h1848, h2430, h2507, h3, hc15, hlam, hphi, u5elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2509 | h2509
                · linarith only [h1, h2073, h2430, h2509, hc34, hlam, hphi, ht45, u5elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2511 | h2511
                  · linarith only [h2, h2430, h2511, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2513 | h2513
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2514 | h2514
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2515 | h2515
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2516 | h2516
                          · linarith only [h0, h1668, h2430, h2513, h2516, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h2073, h2515, h2516, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1668, h2515, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h2514, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2521 | h2521
                      · linarith only [h0, h2320, h2513, h2521, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2521, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h1668 | h1668
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1668
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1668

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 5044000 in
set_option maxHeartbeats 5044000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s2 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

end R2N4
