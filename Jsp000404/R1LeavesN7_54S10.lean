import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S8
import Jsp000404.R1LeavesN7_54S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4448000 in
set_option maxHeartbeats 4448000 in
theorem r1l7_20_12_13_M_LR_L_I_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1115 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1802 | h1802
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1803 | h1803
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1804 | h1804
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1805 | h1805
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1806 | h1806
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1807 | h1807
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1808 | h1808
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1809 | h1809
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1810 | h1810
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1811 | h1811
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1812 | h1812
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1813 | h1813
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1814 | h1814
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1815 | h1815
                            · linarith only [h1802, h1812, h1815, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1802, h1812, h1814, h1815, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1818 | h1818
                            · linarith only [h1802, h1805, h1814, h1818, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases h2bigk with h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h0, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1813, hc35, hlam, hphi, ht0b, ht5b, p1820_1, u0elo1]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                rcases p1820_3 (m.d 0 2) (by simp) with h1824 | h1824
                                · rcases p1820_3 (m.d 1 2) (by simp) with h1825 | h1825
                                  · rcases p1820_3 (m.d 2 3) (by simp) with h1826 | h1826
                                    · linarith only [h1802, h1826, hlam]
                                    · linarith only [h1812, h1826, hlam]
                                  · linarith only [h1808, h1825, hlam]
                                · linarith only [h1824, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                rcases p1820_3 (m.d 0 2) (by simp) with h1831 | h1831
                                · rcases p1820_3 (m.d 1 2) (by simp) with h1832 | h1832
                                  · rcases p1820_3 (m.d 2 3) (by simp) with h1833 | h1833
                                    · linarith only [h1802, h1833, hlam]
                                    · linarith only [h1813, h1833, hlam]
                                  · linarith only [h1809, h1832, hlam]
                                · linarith only [h1831, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1115, h1802, hc12, hlam, hphi, ht01, p1820_1, u0ehi5]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                rcases p1820_3 (m.d 0 2) (by simp) with h1840 | h1840
                                · linarith only [h0, h1840, hlam]
                                · linarith only [h1802, h1840, hlam]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                rcases p1820_3 (m.d 0 2) (by simp) with h1843 | h1843
                                · linarith only [h0, h1843, hlam]
                                · linarith only [h1803, h1843, hlam]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                rcases p1820_3 (m.d 0 2) (by simp) with h1846 | h1846
                                · linarith only [h0, h1846, hlam]
                                · linarith only [h1804, h1846, hlam]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1802, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1807, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1802, h1812, hc34, hlam, hphi, ht0b, ht45, ht5b, p1820_1, u0elo1]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1802, h1813, h1818, hc34, hlam, hphi, ht0b, ht45, ht5b, p1820_1, u0elo1]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1803, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1808, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1812, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1814, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1804, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1809, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1813, hlam, p1820_0]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [h1804, h1812, hc34, hlam, hphi, ht0b, ht45, ht5b, p1820_1, u0elo1]
                              · have p1820_0 := h1820c.1
                                have p1820_1 := h1820c.2.1
                                have p1820_2 := h1820c.2.2.1
                                have p1820_3 := h1820c.2.2.2
                                linarith only [hlam, p1820_0]
                        · linarith only [h1806, h1812, h1813, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1865 | h1865
                        · linarith only [h1802, h1805, h1812, h1865, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1867 | h1867
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1868 | h1868
                            · rcases h2bigk with h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h0, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                rcases p1869_3 (m.d 0 2) (by simp) with h1872 | h1872
                                · rcases p1869_3 (m.d 1 2) (by simp) with h1873 | h1873
                                  · rcases p1869_3 (m.d 2 3) (by simp) with h1874 | h1874
                                    · linarith only [h1874, hlam, p1869_0]
                                    · rcases p1869_3 (m.d 2 4) (by simp) with h1876 | h1876
                                      · linarith only [h1803, h1876, hlam]
                                      · linarith only [h1812, h1876, hlam]
                                  · linarith only [h1807, h1873, hlam]
                                · linarith only [h1872, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1867, hc45, hlam, hphi, ht0b, ht5b, p1869_1, u0elo1]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                rcases p1869_3 (m.d 0 2) (by simp) with h1882 | h1882
                                · rcases p1869_3 (m.d 1 2) (by simp) with h1883 | h1883
                                  · rcases p1869_3 (m.d 2 3) (by simp) with h1884 | h1884
                                    · linarith only [h1802, h1884, hlam]
                                    · rcases p1869_3 (m.d 2 4) (by simp) with h1886 | h1886
                                      · linarith only [h1803, h1886, hlam]
                                      · linarith only [h1867, h1886, hlam]
                                  · linarith only [h1809, h1883, hlam]
                                · linarith only [h1882, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1802, h1805, h1865, h1868, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1869_1]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                rcases p1869_3 (m.d 0 2) (by simp) with h1893 | h1893
                                · linarith only [h0, h1893, hlam]
                                · linarith only [h1802, h1893, hlam]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                rcases p1869_3 (m.d 0 2) (by simp) with h1896 | h1896
                                · linarith only [h0, h1896, hlam]
                                · linarith only [h1803, h1896, hlam]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                rcases p1869_3 (m.d 0 2) (by simp) with h1899 | h1899
                                · linarith only [h0, h1899, hlam]
                                · linarith only [h1804, h1899, hlam]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1802, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1807, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1812, hlam, p1869_1]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1865, hlam, p1869_1]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1803, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1808, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1869_1, u0elo1]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1805, h1812, hc25, hlam, hphi, ht0b, ht5b, p1869_1, u0elo2]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1804, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1809, hlam, p1869_0]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1804, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1869_1, u0elo1]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [h1867, hlam, p1869_1]
                              · have p1869_0 := h1869c.1
                                have p1869_1 := h1869c.2.1
                                have p1869_2 := h1869c.2.2.1
                                have p1869_3 := h1869c.2.2.2
                                linarith only [hlam, p1869_0]
                            · linarith only [h1812, h1867, h1868, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1918 | h1918
                            · linarith only [h1802, h1805, h1867, h1918, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases h2bigk with h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h0, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 2) (by simp) with h1923 | h1923
                                · rcases p1920_3 (m.d 1 2) (by simp) with h1924 | h1924
                                  · rcases p1920_3 (m.d 2 3) (by simp) with h1925 | h1925
                                    · linarith only [h1925, hlam, p1920_0]
                                    · rcases p1920_3 (m.d 2 4) (by simp) with h1927 | h1927
                                      · linarith only [h1803, h1927, hlam]
                                      · linarith only [h1812, h1927, hlam]
                                  · linarith only [h1807, h1924, hlam]
                                · linarith only [h1923, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 2) (by simp) with h1932 | h1932
                                · rcases p1920_3 (m.d 1 2) (by simp) with h1933 | h1933
                                  · rcases p1920_3 (m.d 2 3) (by simp) with h1934 | h1934
                                    · linarith only [h1802, h1934, hlam]
                                    · rcases p1920_3 (m.d 2 4) (by simp) with h1936 | h1936
                                      · linarith only [h1936, hlam, p1920_0]
                                      · rcases p1920_3 (m.d 2 5) (by simp) with h1938 | h1938
                                        · linarith only [h1804, h1938, hlam]
                                        · linarith only [h1867, h1938, hlam]
                                  · linarith only [h1808, h1933, hlam]
                                · linarith only [h1932, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 2) (by simp) with h1943 | h1943
                                · rcases p1920_3 (m.d 1 2) (by simp) with h1944 | h1944
                                  · rcases p1920_3 (m.d 2 3) (by simp) with h1945 | h1945
                                    · linarith only [h1802, h1945, hlam]
                                    · rcases p1920_3 (m.d 2 4) (by simp) with h1947 | h1947
                                      · linarith only [h1803, h1947, hlam]
                                      · rcases p1920_3 (m.d 2 5) (by simp) with h1949 | h1949
                                        · linarith only [h1949, hlam, p1920_0]
                                        · rcases h2emax with h1951 | h1951 | h1951 | h1951 | h1951
                                          · linarith only [h1951, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1920_1]
                                          · linarith only [h0, h1951, hlam, ht01, ht12, u0ehi5]
                                          · rcases h3bigk with h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1115, hlam, p1954_1]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              rcases p1954_3 (m.d 0 3) (by simp) with h1957 | h1957
                                              · rcases p1954_3 (m.d 1 3) (by simp) with h1958 | h1958
                                                · rcases p1954_3 (m.d 2 3) (by simp) with h1959 | h1959
                                                  · linarith only [h1802, h1959, hlam]
                                                  · rcases p1954_3 (m.d 3 4) (by simp) with h1961 | h1961
                                                    · linarith only [h1805, h1961, hlam]
                                                    · linarith only [h1812, h1961, hlam]
                                                · linarith only [h1807, h1958, hlam]
                                              · linarith only [h1802, h1957, hlam]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1802, h1812, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1954_1, u0elo1]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1802, h1812, h1918, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1954_1, u0elo1]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1807, hc12, hlam, hphi, ht01, p1954_1, u0ehi7]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              rcases p1954_3 (m.d 0 3) (by simp) with h1970 | h1970
                                              · linarith only [h1115, h1970, hlam]
                                              · linarith only [h1802, h1970, hlam]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              rcases p1954_3 (m.d 0 3) (by simp) with h1973 | h1973
                                              · linarith only [h1115, h1973, hlam]
                                              · linarith only [h1805, h1973, hlam]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              rcases p1954_3 (m.d 0 3) (by simp) with h1976 | h1976
                                              · linarith only [h1115, h1976, hlam]
                                              · linarith only [h1806, h1976, hlam]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1802, hlam, p1954_1]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1807, hlam, p1954_1]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1812, hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1865, hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1805, hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1810, hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1806, h1918, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1954_1, u0elo2]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1918, hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1806, hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1811, hlam, p1954_0]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1802, h1806, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1954_1, u0elo1]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [h1802, h1806, hc34, hlam, hphi, ht0b, ht45, ht5b, p1954_1, u0elo1]
                                            · have p1954_0 := h1954c.1
                                              have p1954_1 := h1954c.2.1
                                              have p1954_2 := h1954c.2.2.1
                                              have p1954_3 := h1954c.2.2.2
                                              linarith only [hlam, p1954_0]
                                          · rcases h3bigk with h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1115, hlam, p1994_1]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              rcases p1994_3 (m.d 0 3) (by simp) with h1997 | h1997
                                              · rcases p1994_3 (m.d 1 3) (by simp) with h1998 | h1998
                                                · rcases p1994_3 (m.d 2 3) (by simp) with h1999 | h1999
                                                  · linarith only [h1802, h1999, hlam]
                                                  · rcases p1994_3 (m.d 3 4) (by simp) with h2001 | h2001
                                                    · linarith only [h1805, h2001, hlam]
                                                    · linarith only [h1812, h2001, hlam]
                                                · linarith only [h1807, h1998, hlam]
                                              · linarith only [h1802, h1997, hlam]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1802, h1812, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1994_1, u0elo1]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1802, h1865, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1994_1, u0elo1]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1807, hc12, hlam, hphi, ht01, p1994_1, u0ehi7]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              rcases p1994_3 (m.d 0 3) (by simp) with h2010 | h2010
                                              · linarith only [h1115, h2010, hlam]
                                              · linarith only [h1802, h2010, hlam]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              rcases p1994_3 (m.d 0 3) (by simp) with h2013 | h2013
                                              · linarith only [h1115, h2013, hlam]
                                              · linarith only [h1805, h2013, hlam]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              rcases p1994_3 (m.d 0 3) (by simp) with h2016 | h2016
                                              · linarith only [h1115, h2016, hlam]
                                              · linarith only [h1806, h2016, hlam]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1802, hlam, p1994_1]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1807, hlam, p1994_1]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1812, hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1865, hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1805, hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1810, hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1806, h1918, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1994_1, u0elo2]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1918, hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1806, hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1811, hlam, p1994_0]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1802, h1806, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1994_1, u0elo1]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [h1802, h1806, hc34, hlam, hphi, ht0b, ht45, ht5b, p1994_1, u0elo1]
                                            · have p1994_0 := h1994c.1
                                              have p1994_1 := h1994c.2.1
                                              have p1994_2 := h1994c.2.2.1
                                              have p1994_3 := h1994c.2.2.2
                                              linarith only [hlam, p1994_0]
                                          · rcases h3bigk with h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1115, hlam, p2034_1]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              rcases p2034_3 (m.d 0 3) (by simp) with h2037 | h2037
                                              · rcases p2034_3 (m.d 1 3) (by simp) with h2038 | h2038
                                                · rcases p2034_3 (m.d 2 3) (by simp) with h2039 | h2039
                                                  · linarith only [h1802, h2039, hlam]
                                                  · rcases p2034_3 (m.d 3 4) (by simp) with h2041 | h2041
                                                    · linarith only [h1805, h2041, hlam]
                                                    · linarith only [h1812, h2041, hlam]
                                                · linarith only [h1807, h2038, hlam]
                                              · linarith only [h1802, h2037, hlam]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1802, h1812, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2034_1, u0elo1]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1802, h1865, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2034_1, u0elo1]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1807, hc12, hlam, hphi, ht01, p2034_1, u0ehi7]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              rcases p2034_3 (m.d 0 3) (by simp) with h2050 | h2050
                                              · linarith only [h1115, h2050, hlam]
                                              · linarith only [h1802, h2050, hlam]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              rcases p2034_3 (m.d 0 3) (by simp) with h2053 | h2053
                                              · linarith only [h1115, h2053, hlam]
                                              · linarith only [h1805, h2053, hlam]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              rcases p2034_3 (m.d 0 3) (by simp) with h2056 | h2056
                                              · linarith only [h1115, h2056, hlam]
                                              · linarith only [h1806, h2056, hlam]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1802, hlam, p2034_1]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1807, hlam, p2034_1]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1812, hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1865, hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1805, hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1810, hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1806, h1918, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2034_1, u0elo2]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1918, hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1806, hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1811, hlam, p2034_0]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1802, h1806, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2034_1, u0elo1]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [h1802, h1806, hc34, hlam, hphi, ht0b, ht45, ht5b, p2034_1, u0elo1]
                                            · have p2034_0 := h2034c.1
                                              have p2034_1 := h2034c.2.1
                                              have p2034_2 := h2034c.2.2.1
                                              have p2034_3 := h2034c.2.2.2
                                              linarith only [hlam, p2034_0]
                                  · linarith only [h1809, h1944, hlam]
                                · linarith only [h1943, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p1920_1, u0ehi6]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 2) (by simp) with h2078 | h2078
                                · linarith only [h0, h2078, hlam]
                                · linarith only [h1802, h2078, hlam]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 2) (by simp) with h2081 | h2081
                                · linarith only [h0, h2081, hlam]
                                · linarith only [h1803, h2081, hlam]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 2) (by simp) with h2084 | h2084
                                · linarith only [h0, h2084, hlam]
                                · linarith only [h1804, h2084, hlam]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1802, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1807, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1812, hlam, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1865, hlam, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1803, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1808, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1920_1, u0elo1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1867, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1804, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1809, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1806, h1865, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1920_1, u0elo2]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1802, h1806, h1865, hc24, hlam, hphi, ht0b, ht45, ht5b, p1920_1, u0elo1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                    · linarith only [h1115, h1802, h1806, h1811, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h1115, h1810, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h0, h1809, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h1115, h1807, h1808, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1807, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2107 | h2107
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2108 | h2108
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2109 | h2109
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2110 | h2110
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2111 | h2111
                    · linarith only [h1806, h2107, h2111, hc12, hlam, hphi, ht01, u0ehi7]
                    · linarith only [h1115, h2111, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h1115, h1805, h2110, hlam, hphi, u0ehi5, u0elo2]
                · linarith only [h0, h1804, h2109, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h1115, h1803, h2107, h2108, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h1802, h2107, hlam, hphi, u0ehi5, u0elo1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2118 | h2118
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2119 | h2119
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2120 | h2120
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2121 | h2121
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2122 | h2122
                  · linarith only [h1805, h2119, h2122, hc12, hlam, hphi, ht01, u0ehi7]
                  · linarith only [h1115, h2122, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h0, h1804, h2121, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h1115, h1803, h2119, h2120, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h1802, h2119, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2128 | h2128
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2129 | h2129
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2130 | h2130
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2131 | h2131
                  · linarith only [h1115, h1805, h2128, h2131, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h1115, h2131, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h0, h1804, h2130, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h1115, h1803, h2128, h2129, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h1802, h2128, hlam, hphi, u0ehi5, u0elo1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2137 | h2137
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2138 | h2138
          · linarith only [h1802, h1804, h2138, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2140 | h2140
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2141 | h2141
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2142 | h2142
                · linarith only [h1804, h2142, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h2142, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h1115, h1803, h2140, h2141, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h1802, h1804, h2140, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2147 | h2147
          · linarith only [h1802, h1804, h2147, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2149 | h2149
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2150 | h2150
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2151 | h2151
                · linarith only [h1804, h2151, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h2151, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h1115, h1803, h2149, h2150, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h1802, h1804, h2149, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2156 | h2156
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2157 | h2157
        · linarith only [h1802, h1803, h2157, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2159 | h2159
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2160 | h2160
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2161 | h2161
              · linarith only [h1803, h2161, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h2161, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h2160, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2165 | h2165
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2166 | h2166
              · linarith only [h1803, h2166, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h2166, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1802, h2165, hlam, hphi, u0ehi5, u0elo1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2170 | h2170
        · linarith only [h1802, h1803, h2170, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2172 | h2172
          · linarith only [h1802, h2156, h2172, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2174 | h2174
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2175 | h2175
              · linarith only [h1803, h2175, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h2175, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1802, h2174, hlam, hphi, u0ehi5, u0elo1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2179 | h2179
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2180 | h2180
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2181 | h2181
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2182 | h2182
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2183 | h2183
            · linarith only [h1802, h2183, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h2183, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h1802, h2180, h2182, hlam]
        · linarith only [h1802, h2179, h2181, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2188 | h2188
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2189 | h2189
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2190 | h2190
            · linarith only [h1802, h2190, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h2190, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2193 | h2193
            · linarith only [h1802, h2193, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h2193, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · linarith only [h1802, h2179, h2188, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2197 | h2197
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2198 | h2198
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2199 | h2199
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2200 | h2200
            · linarith only [h0, h1802, h2200, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h2200, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h2179, h2197, h2198, h2199, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2204 | h2204
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2205 | h2205
            · linarith only [h0, h1802, h2205, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h2205, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h1802, h2197, h2204, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2209 | h2209
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2210 | h2210
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2211 | h2211
            · linarith only [h1802, h2211, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h2211, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2214 | h2214
            · linarith only [h0, h1802, h2214, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h2214, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2217 | h2217
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2218 | h2218
            · linarith only [h0, h1802, h2218, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h2218, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2221 | h2221
            · linarith only [h0, h1802, h2221, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h2221, hc23, hlam, hphi, ht01, ht12, u0ehi5]

set_option maxHeartbeats 4448000 in
set_option maxHeartbeats 4448000 in
theorem r1l7_20_12_13_M_LR_L_I_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1115 | h1115
  · exact r1l7_20_12_13_M_LR_L_I_L_I_x1_x0 m hb0 hb2 hb3 h0 h1115
  · exact r1l7_20_12_13_M_LR_L_I_L_I_x1_x1 m hb0 hb2 hb3 h0 h1115

set_option maxHeartbeats 4448000 in
set_option maxHeartbeats 4448000 in
theorem r1l7_20_12_13_M_LR_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_M_LR_L_I_L_I_x0 m hb0 hb2 hb3 h0
  · exact r1l7_20_12_13_M_LR_L_I_L_I_x1 m hb0 hb2 hb3 h0

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h10, h12, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · rcases h1bigk with h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h12, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h0, hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h12, h7, h9, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h0, h12, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h1, hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h4, hlam, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h12, h9, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h0, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h2, hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h5, hlam, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h7, hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h2, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h3, hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h6, hlam, p14_1]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h8, hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [h9, hlam, p14_0]
                  · have p14_0 := h14c.1
                    have p14_1 := h14c.2.1
                    have p14_2 := h14c.2.2.1
                    have p14_3 := h14c.2.2.2
                    linarith only [hlam, p14_0]
              · linarith only [h10, h11, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
              · linarith only [h0, h10, h4, h41, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                · rcases h1bigk with h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h43, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h43, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h41, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h0, hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h43, h7, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h0, h41, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h1, hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h4, hlam, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h1, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h0, h4, h41, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h2, hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h5, hlam, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h7, hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h41, h8, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h3, hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h6, hlam, p44_1]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h8, hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [h9, hlam, p44_0]
                  · have p44_0 := h44c.1
                    have p44_1 := h44c.2.1
                    have p44_2 := h44c.2.2.1
                    have p44_3 := h44c.2.2.2
                    linarith only [hlam, p44_0]
                · linarith only [h10, h43, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
            · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
              · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                · linarith only [h7, h73, h9, hlam]
                · rcases h1bigk with h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h4, h72, hc01, hc35, hlam, hphi, ht0b, ht5b, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    rcases p75_3 (m.d 0 1) (by simp) with h79 | h79
                    · rcases p75_3 (m.d 1 2) (by simp) with h80 | h80
                      · linarith only [h0, h80, hlam]
                      · linarith only [h5, h80, hlam]
                    · linarith only [h79, hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    rcases p75_3 (m.d 0 1) (by simp) with h84 | h84
                    · rcases p75_3 (m.d 1 2) (by simp) with h85 | h85
                      · linarith only [h0, h85, hlam]
                      · linarith only [h6, h85, hlam]
                    · linarith only [h84, hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h0, hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h4, h72, h73, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h1, hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h4, hlam, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h1, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h0, h4, h6, h72, h73, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h2, hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h5, hlam, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h7, hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h9, hlam, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h3, hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h6, hlam, p75_1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h8, hlam, p75_0]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [h5, hc24, hlam, hphi, ht45, p75_1, u5elo1]
                  · have p75_0 := h75c.1
                    have p75_1 := h75c.2.1
                    have p75_2 := h75c.2.2.1
                    have p75_3 := h75c.2.2.2
                    linarith only [hlam, p75_0]
              · linarith only [h0, h4, h71, h72, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h7, h71, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
        · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
          · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
            · linarith only [h0, h112, h114, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
              · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
                · rcases h1bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h116, h117, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h116, h117, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h116, h117, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    rcases p118_3 (m.d 0 1) (by simp) with h123 | h123
                    · rcases p118_3 (m.d 1 2) (by simp) with h124 | h124
                      · linarith only [h0, h124, hlam]
                      · linarith only [h124, h6, hlam]
                    · linarith only [h123, hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h0, hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h116, h117, h4, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h0, h116, h117, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h1, hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h4, hlam, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h7, hlam, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h6, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h2, hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h5, hlam, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h0, h112, h117, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h3, hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h6, hlam, p118_1]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h112, hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [h113, hlam, p118_0]
                  · have p118_0 := h118c.1
                    have p118_1 := h118c.2.1
                    have p118_2 := h118c.2.2.1
                    have p118_3 := h118c.2.2.2
                    linarith only [hlam, p118_0]
                · linarith only [h114, h116, h117, h5, h7, hc35, hlam, hphi, u5elo4]
              · linarith only [h112, h116, h7, hc23, hc34, hlam, hphi]
          · linarith only [h112, h113, h7, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h151 | h151
          · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
            · linarith only [h0, h152, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h154 | h154
              · linarith only [h112, h154, h4, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                · rcases h1bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    rcases p157_3 (m.d 0 1) (by simp) with h160 | h160
                    · rcases p157_3 (m.d 1 2) (by simp) with h161 | h161
                      · linarith only [h0, h161, hlam]
                      · linarith only [h161, h4, hlam]
                    · linarith only [h160, hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h151, hc01, hc45, hlam, hphi, ht0b, ht5b, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    rcases p157_3 (m.d 0 1) (by simp) with h166 | h166
                    · rcases p157_3 (m.d 1 2) (by simp) with h167 | h167
                      · linarith only [h0, h167, hlam]
                      · linarith only [h167, h6, hlam]
                    · linarith only [h166, hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h0, hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h0, h151, hc01, hc45, hlam, hphi, ht0b, ht5b, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h1, hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h4, hlam, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h7, hlam, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h112, hlam, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h2, hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h5, hlam, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h0, h154, h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h3, hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h6, hlam, p157_1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h4, hc23, hlam, hphi, ht34, ht45, p157_1, u5elo1]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [h151, hlam, p157_0]
                  · have p157_0 := h157c.1
                    have p157_1 := h157c.2.1
                    have p157_2 := h157c.2.2.1
                    have p157_3 := h157c.2.2.2
                    linarith only [hlam, p157_0]
                · linarith only [h156, h4, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h192 | h192
            · linarith only [h192, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
              · linarith only [h112, h151, h194, h4, h6, h7, hc25, hlam, hphi, u5elo4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
                · rcases h1bigk with h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    rcases p197_3 (m.d 0 1) (by simp) with h200 | h200
                    · rcases p197_3 (m.d 1 2) (by simp) with h201 | h201
                      · linarith only [h0, h201, hlam]
                      · linarith only [h201, h4, hlam]
                    · linarith only [h200, hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    rcases p197_3 (m.d 0 1) (by simp) with h205 | h205
                    · rcases p197_3 (m.d 1 2) (by simp) with h206 | h206
                      · linarith only [h0, h206, hlam]
                      · linarith only [h206, h5, hlam]
                    · linarith only [h205, hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    rcases p197_3 (m.d 0 1) (by simp) with h210 | h210
                    · rcases p197_3 (m.d 1 2) (by simp) with h211 | h211
                      · linarith only [h0, h211, hlam]
                      · linarith only [h211, h6, hlam]
                    · linarith only [h210, hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h0, hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h1, hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h4, hlam, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h7, hlam, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h112, hlam, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h2, hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h5, hlam, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h151, hlam, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h3, hlam, p197_0]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h6, hlam, p197_1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h4, hc23, hlam, hphi, ht34, ht45, p197_1, u5elo1]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [h151, h196, hc14, hlam, hphi, ht45, p197_1, u5elo3]
                  · have p197_0 := h197c.1
                    have p197_1 := h197c.2.1
                    have p197_2 := h197c.2.2.1
                    have p197_3 := h197c.2.2.2
                    linarith only [hlam, p197_0]
                · linarith only [h196, h4, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h237 | h237
    · rcases m.htr 1 3 4 (by decide) (by decide) with h238 | h238
      · linarith only [h238, h4, h5, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
        · rcases m.htr 1 4 5 (by decide) (by decide) with h241 | h241
          · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
            · linarith only [h238, h242, h4, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
              · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                · rcases h1bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h244, h245, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h244, h245, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h244, h245, h4, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    rcases p246_3 (m.d 0 1) (by simp) with h251 | h251
                    · rcases p246_3 (m.d 1 2) (by simp) with h252 | h252
                      · linarith only [h0, h252, hlam]
                      · linarith only [h237, h252, hlam]
                    · linarith only [h251, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h0, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h244, h245, h4, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h5, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h242, h5, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h1, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h4, hlam, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h238, hlam, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h1, h237, hc01, hc25, hlam, hphi, ht0b, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h2, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h2, h242, h244, h245, h4, h5, hc01, hc13, hc34, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h2, h240, h245, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h3, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h237, hlam, p246_1]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h240, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [h241, hlam, p246_0]
                  · have p246_0 := h246c.1
                    have p246_1 := h246c.2.1
                    have p246_2 := h246c.2.2.1
                    have p246_3 := h246c.2.2.2
                    linarith only [hlam, p246_0]
                · linarith only [h242, h244, h245, h4, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
              · linarith only [h240, h242, h244, h4, h5, hc23, hc34, hlam, hphi]
          · linarith only [h241, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h279 | h279
          · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
            · linarith only [h240, h280, h4, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
              · linarith only [h240, h282, h4, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                · rcases h1bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    rcases p285_3 (m.d 0 1) (by simp) with h288 | h288
                    · rcases p285_3 (m.d 1 2) (by simp) with h289 | h289
                      · linarith only [h0, h289, hlam]
                      · linarith only [h289, h4, hlam]
                    · linarith only [h288, hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h237, h282, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    rcases p285_3 (m.d 0 1) (by simp) with h294 | h294
                    · rcases p285_3 (m.d 1 2) (by simp) with h295 | h295
                      · linarith only [h0, h295, hlam]
                      · linarith only [h237, h295, hlam]
                    · linarith only [h294, hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h0, hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h5, hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h280, h5, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h1, hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h4, hlam, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h238, hlam, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h240, hlam, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h2, hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h2, h237, h282, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h3, hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h237, hlam, p285_1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h4, hc23, hlam, hphi, ht34, ht45, p285_1, u5elo1]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [h279, hlam, p285_0]
                  · have p285_0 := h285c.1
                    have p285_1 := h285c.2.1
                    have p285_2 := h285c.2.2.1
                    have p285_3 := h285c.2.2.2
                    linarith only [hlam, p285_0]
                · linarith only [h280, h284, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · linarith only [h279, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h237, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
