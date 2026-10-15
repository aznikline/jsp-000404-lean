import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S3
import Jsp000404.R1LeavesN7_6S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 0 3 5 (by decide) (by decide) with h4008 | h4008
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h4008
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h4008

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 0 3 4 (by decide) (by decide) with h1923 | h1923
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923

set_option maxHeartbeats 6316000 in
set_option maxHeartbeats 6316000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s5 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  rcases m.htr 0 2 5 (by decide) (by decide) with h1799 | h1799
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1800 | h1800
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1801 | h1801
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1802 | h1802
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1803 | h1803
          · linarith only [h0, h1803, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1805 | h1805
            · linarith only [h0, h1270, h1799, h1805, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1807 | h1807
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1808 | h1808
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1809 | h1809
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1810 | h1810
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1811 | h1811
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1812 | h1812
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1813 | h1813
                          · linarith only [h1, h1808, h1813, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1809, h1813, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h1270, h1808, h1809, h1812, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1801, h1811, h4, hlam]
                    · linarith only [h1800, h1810, h4, hlam]
                  · linarith only [h1, h1800, h1802, h1805, h1807, h1809, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h1, h1800, h1803, h1807, h1808, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h1799, h1807, h4, hc12, hc23, hlam, hphi]
        · linarith only [h1270, h1799, h1802, hlam]
      · linarith only [h1799, h1801, h4, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1824 | h1824
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1825 | h1825
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1826 | h1826
          · linarith only [h0, h1826, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1828 | h1828
            · linarith only [h0, h1270, h1800, h1828, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1830 | h1830
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1831 | h1831
                · linarith only [h0, h1, h1800, h1830, h1831, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1833 | h1833
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1834 | h1834
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1835 | h1835
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1836 | h1836
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1837 | h1837
                          · rcases h0bigk with h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h0, h1830, h1835, h1837, hc45, hlam, hphi, ht0b, ht5b, p1838_1, u0elo0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h0, h1830, h1835, h1837, h4, hc45, hlam, hphi, ht0b, ht5b, p1838_1, u0elo0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h0, h1800, h1830, h1835, h1837, h4, hc45, hlam, hphi, ht0b, ht5b, p1838_1, u0elo0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              rcases p1838_3 (m.d 0 1) (by simp) with h1843 | h1843
                              · rcases p1838_3 (m.d 0 2) (by simp) with h1844 | h1844
                                · linarith only [h0, h1844, hlam]
                                · linarith only [h1799, h1844, hlam]
                              · linarith only [h1843, h3, hlam]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h0, hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h4, hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1270, hlam, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1800, h1830, h1834, h1835, h1837, h3, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1, hlam, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1800, h1834, hc02, hc24, hlam, hphi, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1800, hlam, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1800, h1830, h1834, h1835, h1837, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h2, hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h0, h1800, h1830, h1834, h1835, h1837, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h0, h1800, h1830, h1834, h1835, h1837, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              rcases p1838_3 (m.d 0 1) (by simp) with h1862 | h1862
                              · rcases p1838_3 (m.d 0 2) (by simp) with h1863 | h1863
                                · linarith only [h1270, h1863, hlam]
                                · linarith only [h1799, h1863, hlam]
                              · linarith only [h1862, h3, hlam]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h3, hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1799, hlam, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1824, hlam, p1838_0]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [h1825, hlam, p1838_1]
                            · have p1838_0 := h1838c.1
                              have p1838_1 := h1838c.2.1
                              have p1838_2 := h1838c.2.2.1
                              have p1838_3 := h1838c.2.2.2
                              linarith only [hlam, p1838_0]
                          · linarith only [h1800, h1825, h1837, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h1270, h1830, h1833, h1835, h1836, h3, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h1800, h1824, h1835, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1875 | h1875
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1876 | h1876
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1877 | h1877
                          · rcases h0bigk with h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h0, h1830, hc25, hlam, hphi, ht0b, ht5b, p1878_1, u0elo0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1, h1826, h1830, h1875, h1877, hc45, hlam, hphi, ht0b, ht5b, p1878_1, u0elo0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1, h1800, h1826, h1830, h1875, h1877, hc45, hlam, hphi, ht0b, ht5b, p1878_1, u0elo0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              rcases p1878_3 (m.d 0 1) (by simp) with h1883 | h1883
                              · rcases p1878_3 (m.d 0 2) (by simp) with h1884 | h1884
                                · linarith only [h0, h1884, hlam]
                                · linarith only [h1799, h1884, hlam]
                              · linarith only [h1883, h3, hlam]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h0, hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h4, hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1270, hlam, p1878_1]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1830, h1834, h1875, h1877, h3, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1878_1]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1, hlam, p1878_1]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1834, h4, hc02, hc34, hlam, hphi, ht23, p1878_1]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1800, hlam, p1878_1]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              rcases p1878_3 (m.d 0 1) (by simp) with h1897 | h1897
                              · rcases p1878_3 (m.d 0 2) (by simp) with h1898 | h1898
                                · linarith only [h1898, h4, hlam]
                                · linarith only [h1799, h1898, hlam]
                              · linarith only [h1897, h3, hlam]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h2, hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h0, h1830, h1875, h1877, h2, hc45, hlam, hphi, ht0b, ht5b, p1878_1, u0elo0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1, h1826, h1830, h1875, h1877, h2, hc45, hlam, hphi, ht0b, ht5b, p1878_1, u0elo0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              rcases p1878_3 (m.d 0 1) (by simp) with h1906 | h1906
                              · rcases p1878_3 (m.d 0 2) (by simp) with h1907 | h1907
                                · linarith only [h1270, h1907, hlam]
                                · linarith only [h1799, h1907, hlam]
                              · linarith only [h1906, h3, hlam]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h3, hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1799, hlam, p1878_1]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1824, hlam, p1878_0]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [h1825, hlam, p1878_1]
                            · have p1878_0 := h1878c.1
                              have p1878_1 := h1878c.2.1
                              have p1878_2 := h1878c.2.2.1
                              have p1878_3 := h1878c.2.2.2
                              linarith only [hlam, p1878_0]
                          · linarith only [h1834, h1877, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1270, h1830, h1833, h1876, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h0, h1800, h1824, h1830, h1875, h2, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h1825, h1826, h1830, h1831, h1833, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h1799, h1830, h4, hc12, hc23, hlam, hphi]
        · linarith only [h1799, h1800, h1825, h4, hlam]
      · linarith only [h1799, h1824, h4, hlam]
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h1270 h1799

set_option maxHeartbeats 7374000 in
set_option maxHeartbeats 7374000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s4 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h1270 | h1270
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1271 | h1271
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1272 | h1272
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1273 | h1273
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1274 | h1274
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1275 | h1275
            · linarith only [h0, h1275, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1277 | h1277
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1278 | h1278
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1279 | h1279
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1280 | h1280
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1281 | h1281
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1282 | h1282
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1283 | h1283
                          · linarith only [h0, h1277, h1283, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1, h1275, h1277, h1280, h1283, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h1273, h1282, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1272, h1281, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1288 | h1288
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1289 | h1289
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1290 | h1290
                          · linarith only [h0, h1277, h1280, h1290, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1292 | h1292
                            · linarith only [h1277, h1280, h1288, h1292, hlam]
                            · rcases h0bigk with h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1270, h1288, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1270, h1288, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1274, h1277, h1280, h1288, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1274, h1277, h1280, h1288, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h0, hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h4, hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1274, h1277, h1280, h1288, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo1]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1, h1274, h1277, h1280, h1288, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1, hlam, p1294_1]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1, h1270, h1288, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1, h1274, h1277, h1280, h1288, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1, h1274, h1277, h1280, h1288, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h2, hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1270, hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1272, hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1270, h1274, h1277, h1280, h1288, hc34, hlam, hphi, ht0b, ht45, ht5b, p1294_1, u0elo1]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h3, hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1271, hlam, p1294_1]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1273, hlam, p1294_0]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [h1274, hlam, p1294_1]
                              · have p1294_0 := h1294c.1
                                have p1294_1 := h1294c.2.1
                                have p1294_2 := h1294c.2.2.1
                                have p1294_3 := h1294c.2.2.2
                                linarith only [hlam, p1294_0]
                        · linarith only [h1273, h1289, h4, hlam]
                      · linarith only [h1270, h1274, h1280, h1288, h4, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h1272, h1275, h1277, h1279, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h1271, h1277, h1278, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h1270, h1277, h4, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1325 | h1325
            · linarith only [h0, h1325, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1327 | h1327
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1328 | h1328
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1329 | h1329
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1330 | h1330
                    · linarith only [h1274, h1330, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1332 | h1332
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1333 | h1333
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1334 | h1334
                          · linarith only [h1274, h1327, h1334, h2, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1336 | h1336
                            · linarith only [h1274, h1327, h1332, h1336, h2, hlam]
                            · rcases h0bigk with h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h0, h1328, h1332, h1334, hc34, hlam, hphi, ht0b, ht45, ht5b, p1338_1, u0elo0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h1, h1325, h1328, h1332, h1334, hc34, hlam, hphi, ht0b, ht45, ht5b, p1338_1, u0elo0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                rcases p1338_3 (m.d 0 1) (by simp) with h1342 | h1342
                                · rcases p1338_3 (m.d 0 2) (by simp) with h1343 | h1343
                                  · linarith only [h0, h1343, hlam]
                                  · linarith only [h1270, h1343, hlam]
                                · linarith only [h1342, h2, hlam]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                rcases p1338_3 (m.d 0 1) (by simp) with h1347 | h1347
                                · rcases p1338_3 (m.d 0 2) (by simp) with h1348 | h1348
                                  · linarith only [h0, h1348, hlam]
                                  · linarith only [h1271, h1348, hlam]
                                · linarith only [h1347, h3, hlam]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h0, hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h4, hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                rcases p1338_3 (m.d 0 1) (by simp) with h1355 | h1355
                                · rcases p1338_3 (m.d 0 2) (by simp) with h1356 | h1356
                                  · rcases p1338_3 (m.d 0 3) (by simp) with h1357 | h1357
                                    · rcases p1338_3 (m.d 0 4) (by simp) with h1358 | h1358
                                      · linarith only [h1270, h1358, hlam]
                                      · rcases p1338_3 (m.d 0 5) (by simp) with h1360 | h1360
                                        · linarith only [h1271, h1360, hlam]
                                        · linarith only [h1274, h1360, hlam]
                                    · linarith only [h1272, h1357, hlam]
                                  · linarith only [h1270, h1356, hlam]
                                · linarith only [h1355, h2, hlam]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                rcases p1338_3 (m.d 0 1) (by simp) with h1366 | h1366
                                · rcases p1338_3 (m.d 0 2) (by simp) with h1367 | h1367
                                  · rcases p1338_3 (m.d 0 3) (by simp) with h1368 | h1368
                                    · rcases p1338_3 (m.d 0 4) (by simp) with h1369 | h1369
                                      · linarith only [h1270, h1369, hlam]
                                      · rcases p1338_3 (m.d 0 5) (by simp) with h1371 | h1371
                                        · linarith only [h1271, h1371, hlam]
                                        · rcases h0emin with h1373 | h1373 | h1373 | h1373 | h1373
                                          · rcases h2bigk with h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c | h1374c
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1328, h1332, h1334, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1374_1]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h4, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              rcases p1374_3 (m.d 0 2) (by simp) with h1378 | h1378
                                              · rcases p1374_3 (m.d 1 2) (by simp) with h1379 | h1379
                                                · linarith only [h0, h1379, hlam]
                                                · linarith only [h1327, h1379, hlam]
                                              · linarith only [h1378, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              rcases p1374_3 (m.d 0 2) (by simp) with h1383 | h1383
                                              · rcases p1374_3 (m.d 1 2) (by simp) with h1384 | h1384
                                                · linarith only [h0, h1384, hlam]
                                                · linarith only [h1328, h1384, hlam]
                                              · linarith only [h1383, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h0, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1325, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h0, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1374_1, u0elo0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1, h1325, h1332, h1334, hc34, hlam, hphi, ht0b, ht45, ht5b, p1374_1, u0elo0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1274, h1327, h1332, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1338_1, p1374_1]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              rcases p1374_3 (m.d 0 2) (by simp) with h1394 | h1394
                                              · linarith only [h1394, h4, hlam]
                                              · linarith only [h0, h1394, hlam]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1274, h1327, h2, h4, hlam, p1338_1, p1374_2]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1271, h4, hlam, p1338_1, p1374_2]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1270, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1327, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1332, hlam, p1374_1]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1334, hlam, p1374_1]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1271, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1328, hlam, p1374_0]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1333, hlam, p1374_1]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [h1328, h1332, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1338_1, p1374_1, u0elo1]
                                            · have p1374_0 := h1374c.1
                                              have p1374_1 := h1374c.2.1
                                              have p1374_2 := h1374c.2.2.1
                                              have p1374_3 := h1374c.2.2.2
                                              linarith only [hlam, p1374_0]
                                          · rcases h2bigk with h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h4, hc12, hc23, hlam, hphi, p1410_1]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h4, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              rcases p1410_3 (m.d 0 2) (by simp) with h1414 | h1414
                                              · rcases p1410_3 (m.d 1 2) (by simp) with h1415 | h1415
                                                · linarith only [h0, h1415, hlam]
                                                · linarith only [h1327, h1415, hlam]
                                              · linarith only [h1414, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              rcases p1410_3 (m.d 0 2) (by simp) with h1419 | h1419
                                              · rcases p1410_3 (m.d 1 2) (by simp) with h1420 | h1420
                                                · linarith only [h0, h1420, hlam]
                                                · linarith only [h1328, h1420, hlam]
                                              · linarith only [h1419, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h0, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1325, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h0, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1410_1, u0elo0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1, h1325, hc25, hlam, hphi, ht0b, ht5b, p1410_1, u0elo0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1373, hc23, hlam, ht01, ht12, p1410_1]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              rcases p1410_3 (m.d 0 2) (by simp) with h1430 | h1430
                                              · linarith only [h1430, h4, hlam]
                                              · linarith only [h0, h1430, hlam]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1274, h1327, h2, h4, hlam, p1338_1, p1410_2]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1271, h4, hlam, p1338_1, p1410_2]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1270, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1327, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1332, hlam, p1410_1]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1334, hlam, p1410_1]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1271, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1328, hlam, p1410_0]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1333, hlam, p1410_1]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [h1328, h1332, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1338_1, p1410_1, u0elo1]
                                            · have p1410_0 := h1410c.1
                                              have p1410_1 := h1410c.2.1
                                              have p1410_2 := h1410c.2.2.1
                                              have p1410_3 := h1410c.2.2.2
                                              linarith only [hlam, p1410_0]
                                          · rcases h2bigk with h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c | h1446c
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h4, hc12, hc23, hlam, hphi, p1446_1]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h4, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              rcases p1446_3 (m.d 0 2) (by simp) with h1450 | h1450
                                              · rcases p1446_3 (m.d 1 2) (by simp) with h1451 | h1451
                                                · linarith only [h0, h1451, hlam]
                                                · linarith only [h1327, h1451, hlam]
                                              · linarith only [h1450, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              rcases p1446_3 (m.d 0 2) (by simp) with h1455 | h1455
                                              · rcases p1446_3 (m.d 1 2) (by simp) with h1456 | h1456
                                                · linarith only [h0, h1456, hlam]
                                                · linarith only [h1328, h1456, hlam]
                                              · linarith only [h1455, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h0, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1325, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h0, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1446_1, u0elo0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1, h1325, hc25, hlam, hphi, ht0b, ht5b, p1446_1, u0elo0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1338_1, p1446_1]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              rcases p1446_3 (m.d 0 2) (by simp) with h1466 | h1466
                                              · linarith only [h1466, h4, hlam]
                                              · linarith only [h0, h1466, hlam]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1274, h1327, h2, h4, hlam, p1338_1, p1446_2]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1271, h4, hlam, p1338_1, p1446_2]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1270, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1327, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1332, hlam, p1446_1]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1334, hlam, p1446_1]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1271, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1328, hlam, p1446_0]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1333, hlam, p1446_1]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [h1328, h1332, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1338_1, p1446_1, u0elo1]
                                            · have p1446_0 := h1446c.1
                                              have p1446_1 := h1446c.2.1
                                              have p1446_2 := h1446c.2.2.1
                                              have p1446_3 := h1446c.2.2.2
                                              linarith only [hlam, p1446_0]
                                          · linarith only [h1274, h1373, h4, hc23, hlam, ht01, ht12, p1338_1]
                                          · linarith only [h1373, h4, hc23, hlam, ht01, ht12, p1338_1]
                                    · linarith only [h1273, h1368, hlam]
                                  · linarith only [h1271, h1367, hlam]
                                · linarith only [h1366, h3, hlam]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h1, hlam, p1338_1]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h1, h1270, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1338_1, u0elo0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                rcases p1338_3 (m.d 0 1) (by simp) with h1490 | h1490
                                · rcases p1338_3 (m.d 0 2) (by simp) with h1491 | h1491
                                  · linarith only [h1491, h4, hlam]
                                  · linarith only [h1270, h1491, hlam]
                                · linarith only [h1490, h2, hlam]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                rcases p1338_3 (m.d 0 1) (by simp) with h1495 | h1495
                                · rcases p1338_3 (m.d 0 2) (by simp) with h1496 | h1496
                                  · linarith only [h1496, h4, hlam]
                                  · linarith only [h1271, h1496, hlam]
                                · linarith only [h1495, h3, hlam]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h2, hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h1270, hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h1272, hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h1274, hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h3, hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h1271, hlam, p1338_1]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [h1273, hlam, p1338_0]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                rcases p1338_3 (m.d 0 1) (by simp) with h1508 | h1508
                                · rcases p1338_3 (m.d 0 2) (by simp) with h1509 | h1509
                                  · rcases p1338_3 (m.d 0 3) (by simp) with h1510 | h1510
                                    · rcases p1338_3 (m.d 0 4) (by simp) with h1511 | h1511
                                      · linarith only [h1274, h1511, hlam]
                                      · rcases p1338_3 (m.d 0 5) (by simp) with h1513 | h1513
                                        · rcases h0emin with h1514 | h1514 | h1514 | h1514 | h1514
                                          · rcases h2bigk with h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c | h1515c
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1328, h1333, h1336, hc34, hlam, hphi, ht0b, ht45, ht5b, p1515_1, u0elo1]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h4, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              rcases p1515_3 (m.d 0 2) (by simp) with h1519 | h1519
                                              · rcases p1515_3 (m.d 1 2) (by simp) with h1520 | h1520
                                                · linarith only [h0, h1520, hlam]
                                                · linarith only [h1327, h1520, hlam]
                                              · linarith only [h1519, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              rcases p1515_3 (m.d 0 2) (by simp) with h1524 | h1524
                                              · rcases p1515_3 (m.d 1 2) (by simp) with h1525 | h1525
                                                · linarith only [h0, h1525, hlam]
                                                · linarith only [h1328, h1525, hlam]
                                              · linarith only [h1524, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h0, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1325, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h0, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1515_1, u0elo0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1, h1325, h1333, h1336, hc34, hlam, hphi, ht0b, ht45, ht5b, p1515_1, u0elo0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1271, h1327, h1332, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1338_1, p1515_1]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              rcases p1515_3 (m.d 0 2) (by simp) with h1535 | h1535
                                              · linarith only [h1535, h4, hlam]
                                              · linarith only [h0, h1535, hlam]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1271, h1327, h2, h4, hlam, p1338_1, p1515_2]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              rcases p1515_3 (m.d 0 2) (by simp) with h1540 | h1540
                                              · linarith only [h1540, h4, hlam]
                                              · linarith only [h1271, h1540, hlam]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1270, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1327, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1332, hlam, p1515_1]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1334, hlam, p1515_1]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1271, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1328, hlam, p1515_0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h1333, hlam, p1515_1]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [h0, h1328, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1515_1, u0elo0]
                                            · have p1515_0 := h1515c.1
                                              have p1515_1 := h1515c.2.1
                                              have p1515_2 := h1515c.2.2.1
                                              have p1515_3 := h1515c.2.2.2
                                              linarith only [hlam, p1515_0]
                                          · rcases h2bigk with h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h4, hc12, hc23, hlam, hphi, p1553_1]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h4, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              rcases p1553_3 (m.d 0 2) (by simp) with h1557 | h1557
                                              · rcases p1553_3 (m.d 1 2) (by simp) with h1558 | h1558
                                                · linarith only [h0, h1558, hlam]
                                                · linarith only [h1327, h1558, hlam]
                                              · linarith only [h1557, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              rcases p1553_3 (m.d 0 2) (by simp) with h1562 | h1562
                                              · rcases p1553_3 (m.d 1 2) (by simp) with h1563 | h1563
                                                · linarith only [h0, h1563, hlam]
                                                · linarith only [h1328, h1563, hlam]
                                              · linarith only [h1562, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h0, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1325, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h0, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1553_1, u0elo0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1, h1325, h1333, h1336, hc34, hlam, hphi, ht0b, ht45, ht5b, p1553_1, u0elo0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1514, hc23, hlam, ht01, ht12, p1553_1]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              rcases p1553_3 (m.d 0 2) (by simp) with h1573 | h1573
                                              · linarith only [h1573, h4, hlam]
                                              · linarith only [h0, h1573, hlam]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1271, h1327, h2, h4, hlam, p1338_1, p1553_2]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              rcases p1553_3 (m.d 0 2) (by simp) with h1578 | h1578
                                              · linarith only [h1578, h4, hlam]
                                              · linarith only [h1271, h1578, hlam]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1270, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1327, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1332, hlam, p1553_1]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1334, hlam, p1553_1]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1271, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1328, hlam, p1553_0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h1333, hlam, p1553_1]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [h0, h1328, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1553_1, u0elo0]
                                            · have p1553_0 := h1553c.1
                                              have p1553_1 := h1553c.2.1
                                              have p1553_2 := h1553c.2.2.1
                                              have p1553_3 := h1553c.2.2.2
                                              linarith only [hlam, p1553_0]
                                          · rcases h2bigk with h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h4, hc12, hc23, hlam, hphi, p1591_1]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h4, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              rcases p1591_3 (m.d 0 2) (by simp) with h1595 | h1595
                                              · rcases p1591_3 (m.d 1 2) (by simp) with h1596 | h1596
                                                · linarith only [h0, h1596, hlam]
                                                · linarith only [h1327, h1596, hlam]
                                              · linarith only [h1595, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              rcases p1591_3 (m.d 0 2) (by simp) with h1600 | h1600
                                              · rcases p1591_3 (m.d 1 2) (by simp) with h1601 | h1601
                                                · linarith only [h0, h1601, hlam]
                                                · linarith only [h1328, h1601, hlam]
                                              · linarith only [h1600, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h0, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1325, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h0, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1591_1, u0elo0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1, h1325, h1333, h1336, hc34, hlam, hphi, ht0b, ht45, ht5b, p1591_1, u0elo0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1271, h1327, h1332, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1338_1, p1591_1]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              rcases p1591_3 (m.d 0 2) (by simp) with h1611 | h1611
                                              · linarith only [h1611, h4, hlam]
                                              · linarith only [h0, h1611, hlam]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1271, h1327, h2, h4, hlam, p1338_1, p1591_2]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              rcases p1591_3 (m.d 0 2) (by simp) with h1616 | h1616
                                              · linarith only [h1616, h4, hlam]
                                              · linarith only [h1271, h1616, hlam]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1270, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1327, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1332, hlam, p1591_1]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1334, hlam, p1591_1]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1271, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1328, hlam, p1591_0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h1333, hlam, p1591_1]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [h0, h1328, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1591_1, u0elo0]
                                            · have p1591_0 := h1591c.1
                                              have p1591_1 := h1591c.2.1
                                              have p1591_2 := h1591c.2.2.1
                                              have p1591_3 := h1591c.2.2.2
                                              linarith only [hlam, p1591_0]
                                          · linarith only [h1271, h1514, hlam, p1338_1, u0elo1]
                                          · rcases h2bigk with h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h4, hc12, hc23, hlam, hphi, p1630_1]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h4, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              rcases p1630_3 (m.d 0 2) (by simp) with h1634 | h1634
                                              · rcases p1630_3 (m.d 1 2) (by simp) with h1635 | h1635
                                                · linarith only [h0, h1635, hlam]
                                                · linarith only [h1327, h1635, hlam]
                                              · linarith only [h1634, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              rcases p1630_3 (m.d 0 2) (by simp) with h1639 | h1639
                                              · rcases p1630_3 (m.d 1 2) (by simp) with h1640 | h1640
                                                · linarith only [h0, h1640, hlam]
                                                · linarith only [h1328, h1640, hlam]
                                              · linarith only [h1639, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h0, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1325, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h0, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1630_1, u0elo0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1, h1325, h1333, h1336, hc34, hlam, hphi, ht0b, ht45, ht5b, p1630_1, u0elo0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1271, h1327, h1332, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1338_1, p1630_1]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              rcases p1630_3 (m.d 0 2) (by simp) with h1650 | h1650
                                              · linarith only [h1650, h4, hlam]
                                              · linarith only [h0, h1650, hlam]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1271, h1327, h2, h4, hlam, p1338_1, p1630_2]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              rcases p1630_3 (m.d 0 2) (by simp) with h1655 | h1655
                                              · linarith only [h1655, h4, hlam]
                                              · linarith only [h1271, h1655, hlam]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1270, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1327, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1332, hlam, p1630_1]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1334, hlam, p1630_1]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1271, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1328, hlam, p1630_0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h1333, hlam, p1630_1]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [h0, h1328, h1332, hc34, hlam, hphi, ht0b, ht45, ht5b, p1630_1, u0elo0]
                                            · have p1630_0 := h1630c.1
                                              have p1630_1 := h1630c.2.1
                                              have p1630_2 := h1630c.2.2.1
                                              have p1630_3 := h1630c.2.2.2
                                              linarith only [hlam, p1630_0]
                                        · linarith only [h1274, h1513, hlam]
                                    · linarith only [h1272, h1510, hlam]
                                  · linarith only [h1270, h1509, hlam]
                                · linarith only [h1508, h2, hlam]
                              · have p1338_0 := h1338c.1
                                have p1338_1 := h1338c.2.1
                                have p1338_2 := h1338c.2.2.1
                                have p1338_3 := h1338c.2.2.2
                                linarith only [hlam, p1338_0]
                        · linarith only [h1273, h1333, h4, hlam]
                      · linarith only [h1272, h1332, h4, hlam]
                  · linarith only [h1272, h1274, h1325, h1327, h1329, hc24, hc45, hlam, hphi]
                · linarith only [h1271, h1327, h1328, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h1270, h1327, h4, hc12, hc23, hlam, hphi]
        · linarith only [h1271, h1273, h4, hlam]
      · linarith only [h1270, h1272, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1680 | h1680
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1681 | h1681
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1682 | h1682
          · linarith only [h1270, h1271, h1682, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1684 | h1684
            · linarith only [h0, h1684, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1686 | h1686
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1687 | h1687
                · linarith only [h0, h1271, h1687, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1689 | h1689
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1690 | h1690
                    · linarith only [h1682, h1690, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1692 | h1692
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1693 | h1693
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1694 | h1694
                          · linarith only [h1270, h1271, h1682, h1694, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1696 | h1696
                            · linarith only [h0, h1271, h1686, h1692, h1694, h1696, hlam]
                            · rcases h0bigk with h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h0, h1686, h1692, hc34, hlam, hphi, ht0b, ht45, ht5b, p1698_1, u0elo0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h0, h1686, h1692, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p1698_1, u0elo0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                rcases p1698_3 (m.d 0 1) (by simp) with h1702 | h1702
                                · rcases p1698_3 (m.d 0 2) (by simp) with h1703 | h1703
                                  · linarith only [h0, h1703, hlam]
                                  · linarith only [h1270, h1703, hlam]
                                · linarith only [h1702, h2, hlam]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h0, h1271, h1686, h1692, hc34, hlam, hphi, ht0b, ht45, ht5b, p1698_1, u0elo0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h0, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h4, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1271, h1686, h1692, h1694, h2, hc34, hc45, hlam, hphi, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1271, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1, hlam, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h0, h1686, h1692, hc34, hlam, hphi, ht0b, ht45, ht5b, p1698_1, u0elo2]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                rcases p1698_3 (m.d 0 1) (by simp) with h1716 | h1716
                                · rcases p1698_3 (m.d 0 2) (by simp) with h1717 | h1717
                                  · linarith only [h1717, h4, hlam]
                                  · linarith only [h1270, h1717, hlam]
                                · linarith only [h1716, h2, hlam]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h0, h1, h1271, h1686, h1692, hc34, hlam, hphi, ht0b, ht45, ht5b, p1698_1, u0elo0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h2, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1270, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1680, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1682, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h3, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h0, h1686, h1692, hc34, hlam, hphi, ht0b, ht45, ht5b, p1698_1, u0elo4]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1681, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                rcases p1698_3 (m.d 0 1) (by simp) with h1730 | h1730
                                · rcases p1698_3 (m.d 0 2) (by simp) with h1731 | h1731
                                  · linarith only [h1271, h1731, hlam]
                                  · linarith only [h1270, h1731, hlam]
                                · linarith only [h1730, h2, hlam]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                        · linarith only [h0, h1, h1681, h1686, h1692, h1693, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1680, h1686, h1692, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1, h1680, h1684, h1686, h1689, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h1270, h1686, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1740 | h1740
          · linarith only [h1270, h1681, h1740, h4, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1742 | h1742
            · linarith only [h0, h1742, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1744 | h1744
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1745 | h1745
                · linarith only [h0, h1271, h1745, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1747 | h1747
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1748 | h1748
                    · linarith only [h1740, h1748, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1750 | h1750
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1751 | h1751
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1752 | h1752
                          · linarith only [h0, h1740, h1744, h1752, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1754 | h1754
                            · linarith only [h1681, h1744, h1750, h1751, h1752, h1754, h2, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases h0bigk with h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h0, h1744, h1750, hc34, hlam, hphi, ht0b, ht45, ht5b, p1756_1, u0elo0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h0, h1744, h1750, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p1756_1, u0elo0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                rcases p1756_3 (m.d 0 1) (by simp) with h1760 | h1760
                                · rcases p1756_3 (m.d 0 2) (by simp) with h1761 | h1761
                                  · linarith only [h0, h1761, hlam]
                                  · linarith only [h1270, h1761, hlam]
                                · linarith only [h1760, h2, hlam]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1744, h1745, h1750, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1756_1, u0elo0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h0, hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h4, hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1681, h1751, h2, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1756_1]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1271, hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1, hlam, p1756_1]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1681, h1751, hc02, hc23, hlam, hphi, p1756_1]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1270, h1681, h1750, h1751, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1756_1]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1681, hlam, p1756_1]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h2, hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1270, hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1680, hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h1740, hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h3, hlam, p1756_0]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h0, h1744, h1750, hc34, hlam, hphi, ht0b, ht45, ht5b, p1756_1, u0elo4]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [h0, h1681, h1744, h1750, h1751, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1756_1]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                rcases p1756_3 (m.d 0 1) (by simp) with h1784 | h1784
                                · rcases p1756_3 (m.d 0 2) (by simp) with h1785 | h1785
                                  · linarith only [h1271, h1785, hlam]
                                  · linarith only [h1270, h1785, hlam]
                                · linarith only [h1784, h2, hlam]
                              · have p1756_0 := h1756c.1
                                have p1756_1 := h1756c.2.1
                                have p1756_2 := h1756c.2.2.1
                                have p1756_3 := h1756c.2.2.2
                                linarith only [hlam, p1756_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1790 | h1790
                          · linarith only [h0, h1744, h1751, h1790, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1792 | h1792
                            · linarith only [h0, h1271, h1744, h1750, h1751, h1790, h1792, h4, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h1744, h1751, h1792, h4, hc24, hc45, hlam, hphi]
                      · linarith only [h0, h1680, h1744, h1750, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1680, h1681, h1747, hc13, hc35, hlam, hphi]
              · linarith only [h1270, h1744, h4, hc12, hc23, hlam, hphi]
      · linarith only [h1270, h1680, h4, hlam]
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s5 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h1270

end R2N4
