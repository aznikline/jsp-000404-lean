import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h1852 | h1852
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1853 | h1853
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1854 | h1854
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1855 | h1855
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1856 | h1856
          · linarith only [h1856, h2, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1858 | h1858
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1859 | h1859
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1860 | h1860
                · linarith only [h1860, h5, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1862 | h1862
                  · linarith only [h1862, h6, h8, hlam]
                  · rcases h3bigk with h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      rcases p1864_3 (m.d 0 3) (by simp) with h1866 | h1866
                      · rcases p1864_3 (m.d 1 3) (by simp) with h1867 | h1867
                        · linarith only [h1, h1867, hlam]
                        · rcases p1864_3 (m.d 2 3) (by simp) with h1869 | h1869
                          · linarith only [h1869, h4, hlam]
                          · rcases p1864_3 (m.d 3 4) (by simp) with h1871 | h1871
                            · linarith only [h1871, h6, hlam]
                            · rcases p1864_3 (m.d 3 5) (by simp) with h1873 | h1873
                              · linarith only [h1873, h7, hlam]
                              · rcases h4bigk with h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1853, h8, hc24, hc45, hlam, hphi, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h8, hc24, hc45, hlam, hphi, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h8, hc34, hc45, hlam, hphi, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h8, hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h2, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h0, h1854, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1856, hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h5, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1853, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1860, hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h6, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1854, hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1858, hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1862, hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1858, hc34, hc45, hlam, hphi, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                      · linarith only [h1, h1866, hlam]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      rcases p1864_3 (m.d 0 3) (by simp) with h1902 | h1902
                      · rcases p1864_3 (m.d 1 3) (by simp) with h1903 | h1903
                        · linarith only [h1, h1903, hlam]
                        · linarith only [h1852, h1903, hlam]
                      · linarith only [h1902, h4, hlam]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      rcases p1864_3 (m.d 0 3) (by simp) with h1907 | h1907
                      · rcases p1864_3 (m.d 1 3) (by simp) with h1908 | h1908
                        · linarith only [h1, h1908, hlam]
                        · linarith only [h1854, h1908, hlam]
                      · linarith only [h1907, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      rcases p1864_3 (m.d 0 3) (by simp) with h1912 | h1912
                      · rcases p1864_3 (m.d 1 3) (by simp) with h1913 | h1913
                        · linarith only [h1, h1913, hlam]
                        · linarith only [h1855, h1913, hlam]
                      · linarith only [h1912, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h1, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h1, h1859, hc01, hc35, hlam, hphi, ht0b, ht5b, p1864_1]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      rcases p1864_3 (m.d 0 3) (by simp) with h1920 | h1920
                      · rcases p1864_3 (m.d 1 3) (by simp) with h1921 | h1921
                        · rcases p1864_3 (m.d 2 3) (by simp) with h1922 | h1922
                          · linarith only [h1852, h1922, hlam]
                          · linarith only [h1858, h1922, hlam]
                        · linarith only [h1921, hlam, p1864_0]
                      · linarith only [h1920, h6, hlam]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      rcases p1864_3 (m.d 0 3) (by simp) with h1927 | h1927
                      · rcases p1864_3 (m.d 1 3) (by simp) with h1928 | h1928
                        · rcases p1864_3 (m.d 2 3) (by simp) with h1929 | h1929
                          · linarith only [h1852, h1929, hlam]
                          · linarith only [h1859, h1929, hlam]
                        · linarith only [h1928, hlam, p1864_0]
                      · linarith only [h1927, h7, hlam]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h4, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h1852, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h0, h1852, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h0, h1852, h1862, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h6, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h1854, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h1858, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h1862, hlam, p1864_1]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h7, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h1855, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h1859, hlam, p1864_0]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [h0, h1852, h1855, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                    · have p1864_0 := h1864c.1
                      have p1864_1 := h1864c.2.1
                      have p1864_2 := h1864c.2.2.1
                      have p1864_3 := h1864c.2.2.2
                      linarith only [hlam, p1864_0]
              · linarith only [h0, h1852, h1855, h1858, h1859, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1950 | h1950
              · linarith only [h0, h1852, h1854, h1858, h1950, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1952 | h1952
                · linarith only [h0, h1854, h1858, h1952, h2, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1954 | h1954
                  · linarith only [h1854, h1954, h2, h8, hlam]
                  · rcases h3bigk with h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1855, h1858, h1954, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1956_1]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      rcases p1956_3 (m.d 0 3) (by simp) with h1959 | h1959
                      · rcases p1956_3 (m.d 1 3) (by simp) with h1960 | h1960
                        · linarith only [h1, h1960, hlam]
                        · linarith only [h1852, h1960, hlam]
                      · linarith only [h1959, h4, hlam]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      rcases p1956_3 (m.d 0 3) (by simp) with h1964 | h1964
                      · rcases p1956_3 (m.d 1 3) (by simp) with h1965 | h1965
                        · linarith only [h1, h1965, hlam]
                        · linarith only [h1854, h1965, hlam]
                      · linarith only [h1964, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      rcases p1956_3 (m.d 0 3) (by simp) with h1969 | h1969
                      · rcases p1956_3 (m.d 1 3) (by simp) with h1970 | h1970
                        · linarith only [h1, h1970, hlam]
                        · linarith only [h1855, h1970, hlam]
                      · linarith only [h1969, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      rcases p1956_3 (m.d 0 3) (by simp) with h1976 | h1976
                      · rcases p1956_3 (m.d 1 3) (by simp) with h1977 | h1977
                        · rcases p1956_3 (m.d 2 3) (by simp) with h1978 | h1978
                          · linarith only [h1852, h1978, hlam]
                          · rcases p1956_3 (m.d 3 4) (by simp) with h1980 | h1980
                            · linarith only [h1854, h1980, hlam]
                            · linarith only [h1858, h1980, hlam]
                        · linarith only [h1852, h1977, hlam]
                      · linarith only [h1976, h4, hlam]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h0, h1852, h1858, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1956_1]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h0, h1852, h1858, h1954, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1956_1]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h4, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1852, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1858, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1950, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h6, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1854, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1854, h2, h8, hc23, hc45, hlam, hphi, ht34, p1956_1]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1954, hlam, p1956_1]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h7, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h1855, hlam, p1956_0]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h0, h1852, h1855, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1956_1]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [h0, h1852, h1855, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1956_1]
                    · have p1956_0 := h1956c.1
                      have p1956_1 := h1956c.2.1
                      have p1956_2 := h1956c.2.2.1
                      have p1956_3 := h1956c.2.2.2
                      linarith only [hlam, p1956_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2002 | h2002
          · linarith only [h0, h1854, h1855, h2002, h4, h7, h8, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2004 | h2004
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2005 | h2005
              · linarith only [h1852, h1855, h2005, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2007 | h2007
                · linarith only [h1852, h1853, h1855, h2, h2004, h2007, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2009 | h2009
                  · linarith only [h1852, h1855, h2004, h2009, h7, h8, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h3bigk with h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      rcases p2011_3 (m.d 0 3) (by simp) with h2013 | h2013
                      · rcases p2011_3 (m.d 1 3) (by simp) with h2014 | h2014
                        · linarith only [h1, h2014, hlam]
                        · rcases p2011_3 (m.d 2 3) (by simp) with h2016 | h2016
                          · linarith only [h2016, h4, hlam]
                          · rcases p2011_3 (m.d 3 4) (by simp) with h2018 | h2018
                            · linarith only [h2018, h6, hlam]
                            · rcases p2011_3 (m.d 3 5) (by simp) with h2020 | h2020
                              · linarith only [h2020, h7, hlam]
                              · linarith only [h1855, h2020, hlam]
                      · linarith only [h1, h2013, hlam]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      rcases p2011_3 (m.d 0 3) (by simp) with h2024 | h2024
                      · rcases p2011_3 (m.d 1 3) (by simp) with h2025 | h2025
                        · linarith only [h1, h2025, hlam]
                        · linarith only [h1852, h2025, hlam]
                      · linarith only [h2024, h4, hlam]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h1852, h1855, h2004, h7, hlam, p2011_2]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h0, h1852, h1855, h2004, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h1, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h1855, h2004, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2011_1]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h0, h1855, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h1855, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h4, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h1852, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h0, h1852, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h2005, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h6, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h1854, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h2004, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h2009, hlam, p2011_1]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h7, hlam, p2011_0]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h0, h1854, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [h0, h2004, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      rcases p2011_3 (m.d 0 3) (by simp) with h2049 | h2049
                      · rcases p2011_3 (m.d 1 3) (by simp) with h2050 | h2050
                        · linarith only [h1855, h2050, hlam]
                        · linarith only [h1854, h2050, hlam]
                      · linarith only [h2049, h6, hlam]
                    · have p2011_0 := h2011c.1
                      have p2011_1 := h2011c.2.1
                      have p2011_2 := h2011c.2.2.1
                      have p2011_3 := h2011c.2.2.2
                      linarith only [hlam, p2011_0]
            · linarith only [h0, h1854, h1855, h2004, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2056 | h2056
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2057 | h2057
          · linarith only [h1854, h2056, h2057, h6, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h1854, h2056, h2057, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2060 | h2060
          · linarith only [h2, h2060, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2062 | h2062
            · linarith only [h0, h1852, h1854, h2062, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2064 | h2064
              · linarith only [h1852, h2056, h2064, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2066 | h2066
                · linarith only [h2066, h5, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2068 | h2068
                  · linarith only [h2068, h6, h8, hlam]
                  · rcases h3bigk with h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c | h2070c
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      rcases p2070_3 (m.d 0 3) (by simp) with h2072 | h2072
                      · rcases p2070_3 (m.d 1 3) (by simp) with h2073 | h2073
                        · linarith only [h1, h2073, hlam]
                        · rcases p2070_3 (m.d 2 3) (by simp) with h2075 | h2075
                          · linarith only [h2075, h4, hlam]
                          · rcases p2070_3 (m.d 3 4) (by simp) with h2077 | h2077
                            · linarith only [h2077, h6, hlam]
                            · linarith only [h1854, h2077, hlam]
                      · linarith only [h1, h2072, hlam]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      rcases p2070_3 (m.d 0 3) (by simp) with h2081 | h2081
                      · rcases p2070_3 (m.d 1 3) (by simp) with h2082 | h2082
                        · linarith only [h1, h2082, hlam]
                        · linarith only [h1852, h2082, hlam]
                      · linarith only [h2081, h4, hlam]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      rcases p2070_3 (m.d 0 3) (by simp) with h2086 | h2086
                      · rcases p2070_3 (m.d 1 3) (by simp) with h2087 | h2087
                        · linarith only [h1, h2087, hlam]
                        · rcases p2070_3 (m.d 2 3) (by simp) with h2089 | h2089
                          · linarith only [h2089, h4, hlam]
                          · rcases p2070_3 (m.d 3 4) (by simp) with h2091 | h2091
                            · linarith only [h2091, hlam, p2070_0]
                            · rcases p2070_3 (m.d 3 5) (by simp) with h2093 | h2093
                              · linarith only [h2093, h7, hlam]
                              · linarith only [h2068, h2093, hlam]
                      · linarith only [h2086, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      rcases p2070_3 (m.d 0 3) (by simp) with h2097 | h2097
                      · rcases p2070_3 (m.d 1 3) (by simp) with h2098 | h2098
                        · linarith only [h1, h2098, hlam]
                        · rcases p2070_3 (m.d 2 3) (by simp) with h2100 | h2100
                          · linarith only [h2100, h4, hlam]
                          · rcases p2070_3 (m.d 3 4) (by simp) with h2102 | h2102
                            · linarith only [h2102, h6, hlam]
                            · rcases p2070_3 (m.d 3 5) (by simp) with h2104 | h2104
                              · linarith only [h2104, hlam, p2070_0]
                              · rcases h4bigk with h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [hlam, p2106_0]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h8, hc14, hc45, hlam, hphi, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h8, hc24, hc45, hlam, hphi, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h1852, h1854, h8, hc23, hc45, hlam, hphi, ht34, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h8, hlam, p2106_0]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h2, hlam, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [hlam, p2106_0]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h2056, h2060, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p2070_1, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h1854, hlam, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h2060, hlam, p2106_0]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h5, hlam, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h1853, hlam, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [hlam, p2106_0]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h2062, hlam, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h2066, hlam, p2106_0]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h6, hlam, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h6, h8, hc24, hc45, hlam, hphi, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [hlam, p2106_0]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h2068, hlam, p2106_0]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h1852, h1854, hc23, hc45, hlam, hphi, ht34, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h2062, hc23, hc45, hlam, hphi, ht34, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [h1852, h1854, hc23, hc45, hlam, hphi, ht34, p2106_1]
                                · have p2106_0 := h2106c.1
                                  have p2106_1 := h2106c.2.1
                                  have p2106_2 := h2106c.2.2.1
                                  have p2106_3 := h2106c.2.2.2
                                  linarith only [hlam, p2106_0]
                      · linarith only [h2097, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h1, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h1854, hc23, hc34, hlam, hphi, p2070_1]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h1854, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h2056, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h4, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h1852, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h2062, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h2064, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h6, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h6, h8, hc13, hc45, hlam, hphi, ht34, p2070_1]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p2070_1]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h2068, hlam, p2070_1]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h7, hlam, p2070_0]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      rcases p2070_3 (m.d 0 3) (by simp) with h2149 | h2149
                      · rcases p2070_3 (m.d 1 3) (by simp) with h2150 | h2150
                        · linarith only [h2150, hlam, p2070_0]
                        · rcases p2070_3 (m.d 2 3) (by simp) with h2152 | h2152
                          · linarith only [h2064, h2152, hlam]
                          · rcases p2070_3 (m.d 3 4) (by simp) with h2154 | h2154
                            · linarith only [h2068, h2154, hlam]
                            · linarith only [h1854, h2154, hlam]
                      · linarith only [h1, h2149, hlam]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      rcases p2070_3 (m.d 0 3) (by simp) with h2158 | h2158
                      · rcases p2070_3 (m.d 1 3) (by simp) with h2159 | h2159
                        · linarith only [h2056, h2159, hlam]
                        · linarith only [h1852, h2159, hlam]
                      · linarith only [h2158, h4, hlam]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [h1852, h1854, hc23, hc35, hlam, hphi, p2070_1]
                    · have p2070_0 := h2070c.1
                      have p2070_1 := h2070c.2.1
                      have p2070_2 := h2070c.2.2.1
                      have p2070_3 := h2070c.2.2.2
                      linarith only [hlam, p2070_0]
    · linarith only [h1852, h1853, h5, h8, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2166 | h2166
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2167 | h2167
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2168 | h2168
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2169 | h2169
          · linarith only [h2, h2169, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2171 | h2171
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2172 | h2172
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2173 | h2173
                · linarith only [h1852, h2, h2166, h2173, h8, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2175 | h2175
                  · linarith only [h2, h2166, h2171, h2175, h8, hlam]
                  · rcases h3bigk with h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      rcases p2177_3 (m.d 0 3) (by simp) with h2179 | h2179
                      · rcases p2177_3 (m.d 1 3) (by simp) with h2180 | h2180
                        · linarith only [h1, h2180, hlam]
                        · rcases p2177_3 (m.d 2 3) (by simp) with h2182 | h2182
                          · linarith only [h2182, h4, hlam]
                          · linarith only [h1852, h2182, hlam]
                      · linarith only [h1, h2179, hlam]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h0, h1852, h2166, h2171, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2177_1]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      rcases p2177_3 (m.d 0 3) (by simp) with h2187 | h2187
                      · rcases p2177_3 (m.d 1 3) (by simp) with h2188 | h2188
                        · linarith only [h1, h2188, hlam]
                        · linarith only [h2167, h2188, hlam]
                      · linarith only [h2187, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      rcases p2177_3 (m.d 0 3) (by simp) with h2192 | h2192
                      · rcases p2177_3 (m.d 1 3) (by simp) with h2193 | h2193
                        · linarith only [h1, h2193, hlam]
                        · linarith only [h2168, h2193, hlam]
                      · linarith only [h2192, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h1, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h1852, hlam, p2177_1]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      rcases p2177_3 (m.d 0 3) (by simp) with h2200 | h2200
                      · rcases p2177_3 (m.d 1 3) (by simp) with h2201 | h2201
                        · rcases p2177_3 (m.d 2 3) (by simp) with h2202 | h2202
                          · rcases p2177_3 (m.d 3 4) (by simp) with h2203 | h2203
                            · linarith only [h2203, hlam, p2177_0]
                            · rcases p2177_3 (m.d 3 5) (by simp) with h2205 | h2205
                              · linarith only [h2168, h2205, hlam]
                              · linarith only [h2175, h2205, hlam]
                          · linarith only [h2171, h2202, hlam]
                        · linarith only [h2201, hlam, p2177_0]
                      · linarith only [h2200, h6, hlam]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      rcases p2177_3 (m.d 0 3) (by simp) with h2211 | h2211
                      · rcases p2177_3 (m.d 1 3) (by simp) with h2212 | h2212
                        · rcases p2177_3 (m.d 2 3) (by simp) with h2213 | h2213
                          · rcases p2177_3 (m.d 3 4) (by simp) with h2214 | h2214
                            · linarith only [h2167, h2214, hlam]
                            · rcases p2177_3 (m.d 3 5) (by simp) with h2216 | h2216
                              · linarith only [h2216, hlam, p2177_0]
                              · rcases h4bigk with h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2166, h2171, h8, hc34, hc45, hlam, hphi, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2171, h8, hc34, hc45, hlam, hphi, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h8, hc34, hc45, hlam, hphi, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h8, hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2, hlam, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2, h2171, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h0, h1852, h2166, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2169, hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h5, hlam, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2166, hlam, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2173, hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h6, hlam, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2167, hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2171, hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2175, hlam, p2218_0]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2166, hc24, hc45, hlam, hphi, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [h2171, hc34, hc45, hlam, hphi, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p2218_1]
                                · have p2218_0 := h2218c.1
                                  have p2218_1 := h2218c.2.1
                                  have p2218_2 := h2218c.2.2.1
                                  have p2218_3 := h2218c.2.2.2
                                  linarith only [hlam, p2218_0]
                          · linarith only [h2172, h2213, hlam]
                        · linarith only [h2212, hlam, p2177_0]
                      · linarith only [h2211, h7, hlam]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h4, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h0, h1852, h2166, h2171, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2177_1]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      rcases p2177_3 (m.d 0 3) (by simp) with h2250 | h2250
                      · rcases p2177_3 (m.d 1 3) (by simp) with h2251 | h2251
                        · linarith only [h1852, h2251, hlam]
                        · linarith only [h2167, h2251, hlam]
                      · linarith only [h2250, h6, hlam]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      rcases p2177_3 (m.d 0 3) (by simp) with h2255 | h2255
                      · rcases p2177_3 (m.d 1 3) (by simp) with h2256 | h2256
                        · linarith only [h1852, h2256, hlam]
                        · linarith only [h2168, h2256, hlam]
                      · linarith only [h2255, h7, hlam]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h6, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h2167, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h2171, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h2175, hlam, p2177_1]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h7, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h2168, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h2172, hlam, p2177_0]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [h1, h2168, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2177_1]
                    · have p2177_0 := h2177c.1
                      have p2177_1 := h2177c.2.1
                      have p2177_2 := h2177c.2.2.1
                      have p2177_3 := h2177c.2.2.2
                      linarith only [hlam, p2177_0]
              · linarith only [h1852, h2168, h2172, hlam]
            · linarith only [h1852, h2166, h2171, h6, h8, hc24, hc45, hlam, hphi]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2272 | h2272
          · linarith only [h2, h2272, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2274 | h2274
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2275 | h2275
              · linarith only [h0, h1852, h2166, h2168, h2274, h2275, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h1852, h2166, h2274, h2275, h7, h8, hc34, hc45, hlam, hphi]
            · linarith only [h0, h1852, h2166, h2274, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h1852, h2166, h2167, h6, h8, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2280 | h2280
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2281 | h2281
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2282 | h2282
          · linarith only [h1, h2166, h2280, h2282, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2284 | h2284
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2285 | h2285
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2286 | h2286
                · linarith only [h2286, h5, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2288 | h2288
                  · linarith only [h2166, h2280, h2288, h5, h8, hlam]
                  · rcases h3bigk with h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      rcases p2290_3 (m.d 0 3) (by simp) with h2292 | h2292
                      · rcases p2290_3 (m.d 1 3) (by simp) with h2293 | h2293
                        · linarith only [h1, h2293, hlam]
                        · rcases p2290_3 (m.d 2 3) (by simp) with h2295 | h2295
                          · linarith only [h2295, h4, hlam]
                          · linarith only [h1852, h2295, hlam]
                      · linarith only [h1, h2292, hlam]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      rcases p2290_3 (m.d 0 3) (by simp) with h2299 | h2299
                      · rcases p2290_3 (m.d 1 3) (by simp) with h2300 | h2300
                        · linarith only [h1, h2300, hlam]
                        · rcases p2290_3 (m.d 2 3) (by simp) with h2302 | h2302
                          · linarith only [h2302, h4, hlam]
                          · rcases p2290_3 (m.d 3 4) (by simp) with h2304 | h2304
                            · linarith only [h2304, h6, hlam]
                            · rcases p2290_3 (m.d 3 5) (by simp) with h2306 | h2306
                              · linarith only [h2306, h7, hlam]
                              · rcases h4bigk with h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h8, hc14, hc45, hlam, hphi, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2166, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h8, hc34, hc45, hlam, hphi, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h8, hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2, hlam, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2166, hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2282, hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h5, hlam, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h0, h2284, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2290_1, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2286, hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h6, hlam, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2280, hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2284, hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2288, hlam, p2308_0]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2166, hc12, hc45, hlam, hphi, ht23, ht34, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [h2166, hc12, hc45, hlam, hphi, ht23, ht34, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p2308_1]
                                · have p2308_0 := h2308c.1
                                  have p2308_1 := h2308c.2.1
                                  have p2308_2 := h2308c.2.2.1
                                  have p2308_3 := h2308c.2.2.2
                                  linarith only [hlam, p2308_0]
                      · linarith only [h2299, h4, hlam]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      rcases p2290_3 (m.d 0 3) (by simp) with h2335 | h2335
                      · rcases p2290_3 (m.d 1 3) (by simp) with h2336 | h2336
                        · linarith only [h1, h2336, hlam]
                        · linarith only [h2280, h2336, hlam]
                      · linarith only [h2335, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      rcases p2290_3 (m.d 0 3) (by simp) with h2340 | h2340
                      · rcases p2290_3 (m.d 1 3) (by simp) with h2341 | h2341
                        · linarith only [h1, h2341, hlam]
                        · linarith only [h2281, h2341, hlam]
                      · linarith only [h2340, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h1, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h1852, hlam, p2290_1]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      rcases p2290_3 (m.d 0 3) (by simp) with h2348 | h2348
                      · rcases p2290_3 (m.d 1 3) (by simp) with h2349 | h2349
                        · rcases p2290_3 (m.d 2 3) (by simp) with h2350 | h2350
                          · rcases p2290_3 (m.d 3 4) (by simp) with h2351 | h2351
                            · linarith only [h2351, hlam, p2290_0]
                            · rcases p2290_3 (m.d 3 5) (by simp) with h2353 | h2353
                              · linarith only [h2281, h2353, hlam]
                              · linarith only [h2288, h2353, hlam]
                          · linarith only [h2284, h2350, hlam]
                        · linarith only [h2349, hlam, p2290_0]
                      · linarith only [h2348, h6, hlam]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      rcases p2290_3 (m.d 0 3) (by simp) with h2359 | h2359
                      · rcases p2290_3 (m.d 1 3) (by simp) with h2360 | h2360
                        · rcases p2290_3 (m.d 2 3) (by simp) with h2361 | h2361
                          · rcases p2290_3 (m.d 3 4) (by simp) with h2362 | h2362
                            · linarith only [h2280, h2362, hlam]
                            · rcases p2290_3 (m.d 3 5) (by simp) with h2364 | h2364
                              · linarith only [h2364, hlam, p2290_0]
                              · rcases h4bigk with h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h8, hc14, hc45, hlam, hphi, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2166, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h8, hc34, hc45, hlam, hphi, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h8, hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2, hlam, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2166, hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2282, hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h5, hlam, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h5, h8, hc34, hc45, hlam, hphi, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2286, hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h6, hlam, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2280, hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2284, hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2288, hlam, p2366_0]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2166, hc12, hc45, hlam, hphi, ht23, ht34, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [h2166, hc12, hc45, hlam, hphi, ht23, ht34, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p2366_1]
                                · have p2366_0 := h2366c.1
                                  have p2366_1 := h2366c.2.1
                                  have p2366_2 := h2366c.2.2.1
                                  have p2366_3 := h2366c.2.2.2
                                  linarith only [hlam, p2366_0]
                          · linarith only [h2285, h2361, hlam]
                        · linarith only [h2360, hlam, p2290_0]
                      · linarith only [h2359, h7, hlam]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h4, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h0, h2280, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2290_1]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      rcases p2290_3 (m.d 0 3) (by simp) with h2398 | h2398
                      · rcases p2290_3 (m.d 1 3) (by simp) with h2399 | h2399
                        · linarith only [h1852, h2399, hlam]
                        · linarith only [h2280, h2399, hlam]
                      · linarith only [h2398, h6, hlam]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      rcases p2290_3 (m.d 0 3) (by simp) with h2403 | h2403
                      · rcases p2290_3 (m.d 1 3) (by simp) with h2404 | h2404
                        · linarith only [h1852, h2404, hlam]
                        · linarith only [h2281, h2404, hlam]
                      · linarith only [h2403, h7, hlam]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h6, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h2280, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h2284, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h2288, hlam, p2290_1]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h7, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h2281, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h2285, hlam, p2290_0]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [h1, h2281, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2290_1]
                    · have p2290_0 := h2290c.1
                      have p2290_1 := h2290c.2.1
                      have p2290_2 := h2290c.2.2.1
                      have p2290_3 := h2290c.2.2.2
                      linarith only [hlam, p2290_0]
              · linarith only [h1852, h2281, h2285, hlam]
            · linarith only [h1852, h2284, h6, h8, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2420 | h2420
          · linarith only [h2, h2420, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2422 | h2422
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2423 | h2423
              · linarith only [h0, h2280, h2281, h2423, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2425 | h2425
                · linarith only [h2422, h2423, h2425, h7, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2427 | h2427
                  · linarith only [h2166, h2280, h2422, h2423, h2427, h7, h8, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h3bigk with h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      rcases p2429_3 (m.d 0 3) (by simp) with h2431 | h2431
                      · rcases p2429_3 (m.d 1 3) (by simp) with h2432 | h2432
                        · linarith only [h1, h2432, hlam]
                        · rcases p2429_3 (m.d 2 3) (by simp) with h2434 | h2434
                          · linarith only [h2434, h4, hlam]
                          · linarith only [h1852, h2434, hlam]
                      · linarith only [h1, h2431, hlam]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      rcases p2429_3 (m.d 0 3) (by simp) with h2438 | h2438
                      · rcases p2429_3 (m.d 1 3) (by simp) with h2439 | h2439
                        · linarith only [h1, h2439, hlam]
                        · rcases p2429_3 (m.d 2 3) (by simp) with h2441 | h2441
                          · linarith only [h2441, h4, hlam]
                          · rcases p2429_3 (m.d 3 4) (by simp) with h2443 | h2443
                            · linarith only [h2443, h6, hlam]
                            · rcases p2429_3 (m.d 3 5) (by simp) with h2445 | h2445
                              · linarith only [h2445, h7, hlam]
                              · linarith only [h2423, h2445, hlam]
                      · linarith only [h2438, h4, hlam]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h1852, h2280, h2423, h7, hlam, p2429_2]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h2166, h2422, h2423, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h1, hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h1852, hlam, p2429_1]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h0, h1852, h2423, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2429_1]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h2281, hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h4, hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h2423, hc13, hc35, hlam, hphi, p2429_1]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h0, h2423, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2429_1]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h2423, hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h6, hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h2280, hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h2422, hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h2427, hlam, p2429_1]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h7, hlam, p2429_0]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h0, h2280, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2429_1]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [h0, h1852, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      rcases p2429_3 (m.d 0 3) (by simp) with h2469 | h2469
                      · rcases p2429_3 (m.d 1 3) (by simp) with h2470 | h2470
                        · linarith only [h2281, h2470, hlam]
                        · linarith only [h2280, h2470, hlam]
                      · linarith only [h2469, h6, hlam]
                    · have p2429_0 := h2429c.1
                      have p2429_1 := h2429c.2.1
                      have p2429_2 := h2429c.2.2.1
                      have p2429_3 := h2429c.2.2.2
                      linarith only [hlam, p2429_0]
            · linarith only [h1, h1852, h2280, h2422, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2476 | h2476
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2477 | h2477
          · linarith only [h2166, h2477, h5, h8, hlam]
          · linarith only [h2280, h2476, h2477, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2480 | h2480
          · linarith only [h2, h2480, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2482 | h2482
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2483 | h2483
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2484 | h2484
                · linarith only [h2484, h5, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2486 | h2486
                  · linarith only [h2482, h2486, h5, h8, hlam]
                  · rcases h3bigk with h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      rcases p2488_3 (m.d 0 3) (by simp) with h2490 | h2490
                      · rcases p2488_3 (m.d 1 3) (by simp) with h2491 | h2491
                        · linarith only [h1, h2491, hlam]
                        · rcases p2488_3 (m.d 2 3) (by simp) with h2493 | h2493
                          · linarith only [h2493, h4, hlam]
                          · linarith only [h1852, h2493, hlam]
                      · linarith only [h1, h2490, hlam]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h2280, h2483, h2486, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2488_1]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      rcases p2488_3 (m.d 0 3) (by simp) with h2498 | h2498
                      · rcases p2488_3 (m.d 1 3) (by simp) with h2499 | h2499
                        · linarith only [h1, h2499, hlam]
                        · rcases p2488_3 (m.d 2 3) (by simp) with h2501 | h2501
                          · linarith only [h2501, h4, hlam]
                          · linarith only [h2482, h2501, hlam]
                      · linarith only [h2498, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      rcases p2488_3 (m.d 0 3) (by simp) with h2505 | h2505
                      · rcases p2488_3 (m.d 1 3) (by simp) with h2506 | h2506
                        · linarith only [h1, h2506, hlam]
                        · rcases p2488_3 (m.d 2 3) (by simp) with h2508 | h2508
                          · linarith only [h2508, h4, hlam]
                          · linarith only [h2483, h2508, hlam]
                      · linarith only [h2505, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h1, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h1852, hlam, p2488_1]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h2280, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h2476, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h4, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      rcases p2488_3 (m.d 0 3) (by simp) with h2518 | h2518
                      · rcases p2488_3 (m.d 1 3) (by simp) with h2519 | h2519
                        · linarith only [h1852, h2519, hlam]
                        · rcases p2488_3 (m.d 2 3) (by simp) with h2521 | h2521
                          · rcases p2488_3 (m.d 3 4) (by simp) with h2522 | h2522
                            · linarith only [h2482, h2522, hlam]
                            · linarith only [h2280, h2522, hlam]
                          · linarith only [h1852, h2521, hlam]
                      · linarith only [h1, h2518, hlam]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h1852, h2280, hc12, hc23, hlam, hphi, p2488_1]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h0, h1852, h2280, h2486, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2488_1]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h6, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h1852, h2482, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2488_1]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h2482, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h2486, hlam, p2488_1]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h7, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h0, h1852, h2483, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2488_1]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h2483, hlam, p2488_0]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [h0, h2483, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2488_1]
                    · have p2488_0 := h2488c.1
                      have p2488_1 := h2488c.2.1
                      have p2488_2 := h2488c.2.2.1
                      have p2488_3 := h2488c.2.2.2
                      linarith only [hlam, p2488_0]
              · linarith only [h0, h1852, h2280, h2482, h2483, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h1852, h2482, h6, h8, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_13_24_L_I_H_I_s7_x0 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8
  · exact r1l7_13_24_L_I_H_I_s7_x1 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8

end R2N4
