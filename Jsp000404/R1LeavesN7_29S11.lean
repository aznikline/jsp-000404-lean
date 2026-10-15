import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_29S8
import Jsp000404.R1LeavesN7_29S9
import Jsp000404.R1LeavesN7_29S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h947 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1183 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 5 (by decide) (by decide) with h1790 | h1790
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1791 | h1791
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1792 | h1792
      · linarith only [h0, h1790, h1792, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1794 | h1794
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1795 | h1795
          · linarith only [h0, h1795, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1797 | h1797
            · linarith only [h0, h1183, h1790, h1794, h1797, h947, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
            · linarith only [h1792, h1794, h1797, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1800 | h1800
          · linarith only [h0, h1800, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1802 | h1802
            · linarith only [h1, h1183, h1790, h1802, h947, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1804 | h1804
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1805 | h1805
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1806 | h1806
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1807 | h1807
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1808 | h1808
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1809 | h1809
                        · rcases h1bigk with h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            rcases p1810_3 (m.d 0 1) (by simp) with h1812 | h1812
                            · rcases p1810_3 (m.d 1 2) (by simp) with h1813 | h1813
                              · linarith only [h1813, hlam, p1810_0]
                              · rcases p1810_3 (m.d 1 3) (by simp) with h1815 | h1815
                                · linarith only [h1, h1815, hlam]
                                · linarith only [h1792, h1815, hlam]
                            · linarith only [h1812, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1804, h1809, hc45, hlam, hphi, ht01, ht0b, ht5b, p1810_1, u1elo0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1802, h1804, h1809, hc45, hlam, hphi, ht01, ht0b, ht5b, p1810_1, u1elo0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            rcases p1810_3 (m.d 0 1) (by simp) with h1821 | h1821
                            · rcases p1810_3 (m.d 1 2) (by simp) with h1822 | h1822
                              · linarith only [h0, h1822, hlam]
                              · rcases p1810_3 (m.d 1 3) (by simp) with h1824 | h1824
                                · linarith only [h1, h1824, hlam]
                                · linarith only [h1804, h1824, hlam]
                            · linarith only [h1821, hlam, p1810_0]
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
                            linarith only [h1792, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1794, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1800, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1, h1183, h1806, hc12, hc23, hlam, hphi, p1810_1]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1802, hlam, p1810_1]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1, h1183, h1806, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1810_1]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h2, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1810_1, u1elo0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1810_1, u1elo0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1800, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1810_1, u1elo0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h3, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1810_1, u1elo0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1804, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [h1805, hlam, p1810_0]
                          · have p1810_0 := h1810c.1
                            have p1810_1 := h1810c.2.1
                            have p1810_2 := h1810c.2.2.1
                            have p1810_3 := h1810c.2.2.2
                            linarith only [hlam, p1810_0]
                        · linarith only [h1, h1183, h1791, h1804, h1809, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1183, h1805, h1806, h1808, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h1183, h1804, h1807, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1851 | h1851
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1852 | h1852
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1853 | h1853
                        · rcases h1bigk with h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            rcases p1854_3 (m.d 0 1) (by simp) with h1856 | h1856
                            · rcases p1854_3 (m.d 1 2) (by simp) with h1857 | h1857
                              · linarith only [h1857, hlam, p1854_0]
                              · rcases p1854_3 (m.d 1 3) (by simp) with h1859 | h1859
                                · linarith only [h1, h1859, hlam]
                                · linarith only [h1792, h1859, hlam]
                            · linarith only [h1856, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1804, hc35, hlam, hphi, ht01, ht0b, ht5b, p1854_1, u1elo0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1802, h1804, hc35, hlam, hphi, ht01, ht0b, ht5b, p1854_1, u1elo0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            rcases p1854_3 (m.d 0 1) (by simp) with h1865 | h1865
                            · rcases p1854_3 (m.d 1 2) (by simp) with h1866 | h1866
                              · linarith only [h0, h1866, hlam]
                              · rcases p1854_3 (m.d 1 3) (by simp) with h1868 | h1868
                                · linarith only [h1, h1868, hlam]
                                · linarith only [h1804, h1868, hlam]
                            · linarith only [h1865, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h0, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1792, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1794, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1800, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1854_1, u1elo0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1802, hlam, p1854_1]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1802, h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1854_1, u1elo0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h2, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1854_1, u1elo0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1854_1, u1elo0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1800, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1854_1, u1elo0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h3, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1854_1, u1elo0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1804, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [h1805, hlam, p1854_0]
                          · have p1854_0 := h1854c.1
                            have p1854_1 := h1854c.2.1
                            have p1854_2 := h1854c.2.2.1
                            have p1854_3 := h1854c.2.2.2
                            linarith only [hlam, p1854_0]
                        · linarith only [h0, h1806, h1853, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1794, h1805, h1852, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1790, h1851, h4, hlam]
                · linarith only [h1791, h1802, h1804, h1805, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1183, h1790, h1792, h1804, hc12, hc34, hlam, hphi, ht23]
    · linarith only [h1183, h1790, h1791, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1898 | h1898
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1899 | h1899
      · linarith only [h0, h1899, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1901 | h1901
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1902 | h1902
          · linarith only [h0, h1902, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1904 | h1904
            · linarith only [h0, h1183, h1901, h1904, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
            · linarith only [h1899, h1901, h1904, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1907 | h1907
          · linarith only [h1901, h1907, h947, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1909 | h1909
            · linarith only [h1, h1183, h1909, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1911 | h1911
              · linarith only [h1, h1790, h1911, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1913 | h1913
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1914 | h1914
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1915 | h1915
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1916 | h1916
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1917 | h1917
                        · rcases h1bigk with h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            rcases p1918_3 (m.d 0 1) (by simp) with h1920 | h1920
                            · rcases p1918_3 (m.d 1 2) (by simp) with h1921 | h1921
                              · linarith only [h1921, hlam, p1918_0]
                              · rcases p1918_3 (m.d 1 3) (by simp) with h1923 | h1923
                                · linarith only [h1, h1923, hlam]
                                · linarith only [h1899, h1923, hlam]
                            · linarith only [h1920, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            rcases p1918_3 (m.d 0 1) (by simp) with h1927 | h1927
                            · rcases p1918_3 (m.d 1 2) (by simp) with h1928 | h1928
                              · linarith only [h0, h1928, hlam]
                              · rcases p1918_3 (m.d 1 3) (by simp) with h1930 | h1930
                                · linarith only [h1930, hlam, p1918_0]
                                · rcases p1918_3 (m.d 1 4) (by simp) with h1932 | h1932
                                  · linarith only [h1932, h2, hlam]
                                  · linarith only [h1909, h1932, hlam]
                            · linarith only [h1927, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1913, hc45, hlam, hphi, ht01, ht0b, ht5b, p1918_1, u1elo0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            rcases p1918_3 (m.d 0 1) (by simp) with h1937 | h1937
                            · rcases p1918_3 (m.d 1 2) (by simp) with h1938 | h1938
                              · linarith only [h0, h1938, hlam]
                              · rcases p1918_3 (m.d 1 3) (by simp) with h1940 | h1940
                                · linarith only [h1, h1940, hlam]
                                · rcases p1918_3 (m.d 1 4) (by simp) with h1942 | h1942
                                  · linarith only [h1942, h2, hlam]
                                  · linarith only [h1913, h1942, hlam]
                            · linarith only [h1937, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h0, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1899, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1901, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1907, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1, h1790, h1915, hc12, hc25, hlam, hphi, p1918_1]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1909, hlam, p1918_1]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1911, hlam, p1918_1]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h2, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1918_1, u1elo0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1918_1, u1elo0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1918_1, u1elo0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h3, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1918_1, u1elo0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1899, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1918_1, u1elo0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [h1913, hlam, p1918_0]
                          · have p1918_0 := h1918c.1
                            have p1918_1 := h1918c.2.1
                            have p1918_2 := h1918c.2.2.1
                            have p1918_3 := h1918c.2.2.2
                            linarith only [hlam, p1918_0]
                        · linarith only [h1, h1183, h1898, h1899, h1917, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1901, h1913, h1916, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1, h1183, h1899, h1914, h1915, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1969 | h1969
                    · linarith only [h1, h1790, h1899, h1914, h1969, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1971 | h1971
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1972 | h1972
                        · rcases h1bigk with h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            rcases p1973_3 (m.d 0 1) (by simp) with h1975 | h1975
                            · rcases p1973_3 (m.d 1 2) (by simp) with h1976 | h1976
                              · linarith only [h1976, hlam, p1973_0]
                              · rcases p1973_3 (m.d 1 3) (by simp) with h1978 | h1978
                                · linarith only [h1, h1978, hlam]
                                · linarith only [h1899, h1978, hlam]
                            · linarith only [h1975, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            rcases p1973_3 (m.d 0 1) (by simp) with h1982 | h1982
                            · rcases p1973_3 (m.d 1 2) (by simp) with h1983 | h1983
                              · linarith only [h0, h1983, hlam]
                              · rcases p1973_3 (m.d 1 3) (by simp) with h1985 | h1985
                                · linarith only [h1985, hlam, p1973_0]
                                · rcases p1973_3 (m.d 1 4) (by simp) with h1987 | h1987
                                  · linarith only [h1987, h2, hlam]
                                  · linarith only [h1909, h1987, hlam]
                            · linarith only [h1982, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1913, hc45, hlam, hphi, ht01, ht0b, ht5b, p1973_1, u1elo0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            rcases p1973_3 (m.d 0 1) (by simp) with h1992 | h1992
                            · rcases p1973_3 (m.d 1 2) (by simp) with h1993 | h1993
                              · linarith only [h0, h1993, hlam]
                              · rcases p1973_3 (m.d 1 3) (by simp) with h1995 | h1995
                                · linarith only [h1, h1995, hlam]
                                · rcases p1973_3 (m.d 1 4) (by simp) with h1997 | h1997
                                  · linarith only [h1997, h2, hlam]
                                  · linarith only [h1913, h1997, hlam]
                            · linarith only [h1992, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h0, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1899, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1901, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1907, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u1elo0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1909, hlam, p1973_1]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1911, hlam, p1973_1]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h2, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u1elo0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1973_1, u1elo0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1973_1, u1elo0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h3, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u1elo0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1899, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u1elo0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [h1913, hlam, p1973_0]
                          · have p1973_0 := h1973c.1
                            have p1973_1 := h1973c.2.1
                            have p1973_2 := h1973c.2.2.1
                            have p1973_3 := h1973c.2.2.2
                            linarith only [hlam, p1973_0]
                        · linarith only [h0, h1898, h1914, h1971, h1972, h2, h947, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1913, h1971, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2023 | h2023
                  · linarith only [h1183, h1898, h1901, h1913, h2023, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2025 | h2025
                    · linarith only [h0, h1790, h2023, h2025, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2027 | h2027
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2028 | h2028
                        · rcases h1bigk with h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c | h2029c
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            rcases p2029_3 (m.d 0 1) (by simp) with h2031 | h2031
                            · rcases p2029_3 (m.d 1 2) (by simp) with h2032 | h2032
                              · linarith only [h2032, hlam, p2029_0]
                              · rcases p2029_3 (m.d 1 3) (by simp) with h2034 | h2034
                                · linarith only [h1, h2034, hlam]
                                · linarith only [h1899, h2034, hlam]
                            · linarith only [h2031, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            rcases p2029_3 (m.d 0 1) (by simp) with h2038 | h2038
                            · rcases p2029_3 (m.d 1 2) (by simp) with h2039 | h2039
                              · linarith only [h0, h2039, hlam]
                              · rcases p2029_3 (m.d 1 3) (by simp) with h2041 | h2041
                                · linarith only [h2041, hlam, p2029_0]
                                · rcases p2029_3 (m.d 1 4) (by simp) with h2043 | h2043
                                  · linarith only [h2, h2043, hlam]
                                  · linarith only [h1909, h2043, hlam]
                            · linarith only [h2038, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            rcases p2029_3 (m.d 0 1) (by simp) with h2047 | h2047
                            · rcases p2029_3 (m.d 1 2) (by simp) with h2048 | h2048
                              · linarith only [h0, h2048, hlam]
                              · rcases p2029_3 (m.d 1 3) (by simp) with h2050 | h2050
                                · linarith only [h1, h2050, hlam]
                                · rcases p2029_3 (m.d 1 4) (by simp) with h2052 | h2052
                                  · linarith only [h2052, hlam, p2029_0]
                                  · rcases p2029_3 (m.d 1 5) (by simp) with h2054 | h2054
                                    · linarith only [h2054, h3, hlam]
                                    · linarith only [h1913, h2054, hlam]
                            · linarith only [h2047, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            rcases p2029_3 (m.d 0 1) (by simp) with h2058 | h2058
                            · rcases p2029_3 (m.d 1 2) (by simp) with h2059 | h2059
                              · linarith only [h0, h2059, hlam]
                              · rcases p2029_3 (m.d 1 3) (by simp) with h2061 | h2061
                                · linarith only [h1, h2061, hlam]
                                · rcases p2029_3 (m.d 1 4) (by simp) with h2063 | h2063
                                  · linarith only [h2, h2063, hlam]
                                  · rcases p2029_3 (m.d 1 5) (by simp) with h2065 | h2065
                                    · linarith only [h2065, hlam, p2029_0]
                                    · rcases h5bigk with h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        rcases p2067_3 (m.d 0 5) (by simp) with h2069 | h2069
                                        · rcases p2067_3 (m.d 1 5) (by simp) with h2070 | h2070
                                          · linarith only [h2070, h3, hlam]
                                          · rcases p2067_3 (m.d 2 5) (by simp) with h2072 | h2072
                                            · rcases p2067_3 (m.d 3 5) (by simp) with h2073 | h2073
                                              · rcases p2067_3 (m.d 4 5) (by simp) with h2074 | h2074
                                                · linarith only [h1898, h2074, hlam]
                                                · linarith only [h1913, h2074, hlam]
                                              · linarith only [h1911, h2073, hlam]
                                            · linarith only [h1907, h2072, hlam]
                                        · linarith only [h2069, h3, hlam]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h947, hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1790, hlam, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1899, h1909, h1913, h2027, h947, hc12, hc24, hlam, hphi, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h3, hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1907, hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1911, hlam, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1913, hlam, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1898, h1899, h1909, h1913, h2027, hc12, hc24, hlam, hphi, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        rcases p2067_3 (m.d 0 5) (by simp) with h2089 | h2089
                                        · linarith only [h2089, h947, hlam]
                                        · linarith only [h2089, h3, hlam]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h2025, hlam, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1899, h1909, h1913, h2023, h2027, hc12, hc34, hlam, hphi, ht23, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1898, h1899, h1909, h1913, h2028, hc12, hc34, hlam, hphi, ht23, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        rcases p2067_3 (m.d 0 5) (by simp) with h2096 | h2096
                                        · linarith only [h1790, h2096, hlam]
                                        · linarith only [h2096, h3, hlam]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h0, h2028, h947, hc12, hc34, hlam, hphi, ht23, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1899, h1909, h1913, h2028, hc12, hc34, hlam, hphi, ht23, p2067_1]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1898, hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h1898, h1899, h1909, h1913, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2067_1, u1elo0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h2027, hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [h2028, hlam, p2067_0]
                                      · have p2067_0 := h2067c.1
                                        have p2067_1 := h2067c.2.1
                                        have p2067_2 := h2067c.2.2.1
                                        have p2067_3 := h2067c.2.2.2
                                        linarith only [hlam, p2067_0]
                            · linarith only [h2058, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h0, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1899, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1901, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1907, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2029_1, u1elo0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1909, hlam, p2029_1]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1911, hlam, p2029_1]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h2, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1913, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2029_1, u1elo0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1913, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2029_1, u1elo0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1913, hlam, p2029_1]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h3, hlam, p2029_0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2029_1, u1elo0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h1899, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2029_1, u1elo0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2029_1, u1elo0]
                          · have p2029_0 := h2029c.1
                            have p2029_1 := h2029c.2.1
                            have p2029_2 := h2029c.2.2.1
                            have p2029_3 := h2029c.2.2.2
                            linarith only [hlam, p2029_0]
                        · linarith only [h0, h1183, h1898, h2, h2028, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1898, h1901, h2, h2027, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2130 | h2130
      · linarith only [h0, h2130, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2132 | h2132
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2133 | h2133
          · linarith only [h0, h2133, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2135 | h2135
            · linarith only [h0, h1183, h2132, h2135, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
            · linarith only [h2130, h2132, h2135, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2138 | h2138
          · linarith only [h0, h2138, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2140 | h2140
            · linarith only [h1, h1183, h2140, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2142 | h2142
              · linarith only [h1, h1790, h2142, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2144 | h2144
                · linarith only [h1898, h2, h2144, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2146 | h2146
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2147 | h2147
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2148 | h2148
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2149 | h2149
                        · linarith only [h0, h1183, h1898, h2146, h2149, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1183, h2146, h2148, h2149, h4, hc12, hc23, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2152 | h2152
                        · linarith only [h0, h1183, h1898, h2146, h2152, h4, hc12, hc23, hlam, hphi]
                        · rcases h1bigk with h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c | h2154c
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            rcases p2154_3 (m.d 0 1) (by simp) with h2156 | h2156
                            · rcases p2154_3 (m.d 1 2) (by simp) with h2157 | h2157
                              · linarith only [h2157, hlam, p2154_0]
                              · rcases p2154_3 (m.d 1 3) (by simp) with h2159 | h2159
                                · linarith only [h1, h2159, hlam]
                                · linarith only [h2130, h2159, hlam]
                            · linarith only [h2156, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            rcases p2154_3 (m.d 0 1) (by simp) with h2163 | h2163
                            · rcases p2154_3 (m.d 1 2) (by simp) with h2164 | h2164
                              · linarith only [h0, h2164, hlam]
                              · rcases p2154_3 (m.d 1 3) (by simp) with h2166 | h2166
                                · linarith only [h2166, hlam, p2154_0]
                                · rcases p2154_3 (m.d 1 4) (by simp) with h2168 | h2168
                                  · linarith only [h2, h2168, hlam]
                                  · linarith only [h2140, h2168, hlam]
                            · linarith only [h2163, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            rcases p2154_3 (m.d 0 1) (by simp) with h2172 | h2172
                            · rcases p2154_3 (m.d 1 2) (by simp) with h2173 | h2173
                              · linarith only [h0, h2173, hlam]
                              · rcases p2154_3 (m.d 1 3) (by simp) with h2175 | h2175
                                · linarith only [h1, h2175, hlam]
                                · rcases p2154_3 (m.d 1 4) (by simp) with h2177 | h2177
                                  · linarith only [h2177, hlam, p2154_0]
                                  · rcases p2154_3 (m.d 1 5) (by simp) with h2179 | h2179
                                    · linarith only [h2179, h3, hlam]
                                    · linarith only [h2144, h2179, hlam]
                            · linarith only [h2172, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            rcases p2154_3 (m.d 0 1) (by simp) with h2183 | h2183
                            · rcases p2154_3 (m.d 1 2) (by simp) with h2184 | h2184
                              · linarith only [h0, h2184, hlam]
                              · rcases p2154_3 (m.d 1 3) (by simp) with h2186 | h2186
                                · linarith only [h1, h2186, hlam]
                                · rcases p2154_3 (m.d 1 4) (by simp) with h2188 | h2188
                                  · linarith only [h2, h2188, hlam]
                                  · rcases p2154_3 (m.d 1 5) (by simp) with h2190 | h2190
                                    · linarith only [h2190, hlam, p2154_0]
                                    · rcases h5bigk with h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c | h2192c
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [hlam, p2192_0]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h1790, h2138, h2147, hc12, hc23, hlam, hphi, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h947, hlam, p2192_0]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h1790, hlam, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h1898, hlam, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h3, hlam, p2192_0]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [hlam, p2192_0]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h2138, hlam, p2192_0]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h2142, hlam, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h2144, hlam, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        rcases p2192_3 (m.d 0 5) (by simp) with h2203 | h2203
                                        · linarith only [h2203, h947, hlam]
                                        · rcases p2192_3 (m.d 1 5) (by simp) with h2205 | h2205
                                          · linarith only [h2138, h2205, hlam]
                                          · rcases p2192_3 (m.d 2 5) (by simp) with h2207 | h2207
                                            · rcases p2192_3 (m.d 3 5) (by simp) with h2208 | h2208
                                              · linarith only [h2147, h2208, hlam]
                                              · linarith only [h1790, h2208, hlam]
                                            · linarith only [h2207, h947, hlam]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        rcases p2192_3 (m.d 0 5) (by simp) with h2212 | h2212
                                        · linarith only [h2212, h947, hlam]
                                        · linarith only [h2212, h3, hlam]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [hlam, p2192_0]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h0, h1790, h2148, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h2148, hlam, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h0, h2147, h947, hc12, hc23, hlam, hphi, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h2130, h2140, h2144, h2147, hc12, hc23, hlam, hphi, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h2147, hlam, p2192_0]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [hlam, p2192_0]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h2152, hlam, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        rcases p2192_3 (m.d 0 5) (by simp) with h2223 | h2223
                                        · linarith only [h1898, h2223, hlam]
                                        · rcases p2192_3 (m.d 1 5) (by simp) with h2225 | h2225
                                          · linarith only [h2144, h2225, hlam]
                                          · rcases p2192_3 (m.d 2 5) (by simp) with h2227 | h2227
                                            · linarith only [h2148, h2227, hlam]
                                            · linarith only [h2227, h947, hlam]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        rcases p2192_3 (m.d 0 5) (by simp) with h2230 | h2230
                                        · linarith only [h1898, h2230, hlam]
                                        · linarith only [h2230, h3, hlam]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h0, h947, hc12, hc45, hlam, hphi, ht23, ht34, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [h0, h1790, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2192_1]
                                      · have p2192_0 := h2192c.1
                                        have p2192_1 := h2192c.2.1
                                        have p2192_2 := h2192c.2.2.1
                                        have p2192_3 := h2192c.2.2.2
                                        linarith only [hlam, p2192_0]
                            · linarith only [h2183, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h0, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2130, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2132, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2138, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h1, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2154_1, u1elo0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2140, hlam, p2154_1]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2142, hlam, p2154_1]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2154_1, u1elo0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2144, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2154_1, u1elo0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2144, hlam, p2154_1]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h3, hlam, p2154_0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2154_1, u1elo0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h2130, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2154_1, u1elo0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2154_1, u1elo0]
                          · have p2154_0 := h2154c.1
                            have p2154_1 := h2154c.2.1
                            have p2154_2 := h2154c.2.2.1
                            have p2154_3 := h2154c.2.2.2
                            linarith only [hlam, p2154_0]
                    · linarith only [h0, h1183, h2146, h2147, h4, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2258 | h2258
                    · linarith only [h0, h1790, h2146, h2258, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2260 | h2260
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2261 | h2261
                        · rcases h1bigk with h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            rcases p2262_3 (m.d 0 1) (by simp) with h2264 | h2264
                            · rcases p2262_3 (m.d 1 2) (by simp) with h2265 | h2265
                              · linarith only [h2265, hlam, p2262_0]
                              · rcases p2262_3 (m.d 1 3) (by simp) with h2267 | h2267
                                · linarith only [h1, h2267, hlam]
                                · linarith only [h2130, h2267, hlam]
                            · linarith only [h2264, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            rcases p2262_3 (m.d 0 1) (by simp) with h2271 | h2271
                            · rcases p2262_3 (m.d 1 2) (by simp) with h2272 | h2272
                              · linarith only [h0, h2272, hlam]
                              · rcases p2262_3 (m.d 1 3) (by simp) with h2274 | h2274
                                · linarith only [h2274, hlam, p2262_0]
                                · rcases p2262_3 (m.d 1 4) (by simp) with h2276 | h2276
                                  · linarith only [h2, h2276, hlam]
                                  · linarith only [h2140, h2276, hlam]
                            · linarith only [h2271, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            rcases p2262_3 (m.d 0 1) (by simp) with h2280 | h2280
                            · rcases p2262_3 (m.d 1 2) (by simp) with h2281 | h2281
                              · linarith only [h0, h2281, hlam]
                              · rcases p2262_3 (m.d 1 3) (by simp) with h2283 | h2283
                                · linarith only [h1, h2283, hlam]
                                · rcases p2262_3 (m.d 1 4) (by simp) with h2285 | h2285
                                  · linarith only [h2285, hlam, p2262_0]
                                  · rcases p2262_3 (m.d 1 5) (by simp) with h2287 | h2287
                                    · linarith only [h2287, h3, hlam]
                                    · linarith only [h2144, h2287, hlam]
                            · linarith only [h2280, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            rcases p2262_3 (m.d 0 1) (by simp) with h2291 | h2291
                            · rcases p2262_3 (m.d 1 2) (by simp) with h2292 | h2292
                              · linarith only [h0, h2292, hlam]
                              · rcases p2262_3 (m.d 1 3) (by simp) with h2294 | h2294
                                · linarith only [h1, h2294, hlam]
                                · rcases p2262_3 (m.d 1 4) (by simp) with h2296 | h2296
                                  · linarith only [h2, h2296, hlam]
                                  · rcases p2262_3 (m.d 1 5) (by simp) with h2298 | h2298
                                    · linarith only [h2298, hlam, p2262_0]
                                    · rcases h5bigk with h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c | h2300c
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h1898, h2138, h2260, hc12, hc24, hlam, hphi, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h947, hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h1790, hlam, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h1898, hlam, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h3, hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h2138, hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h2142, hlam, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h2144, hlam, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        rcases p2300_3 (m.d 0 5) (by simp) with h2311 | h2311
                                        · linarith only [h2311, h947, hlam]
                                        · rcases p2300_3 (m.d 1 5) (by simp) with h2313 | h2313
                                          · linarith only [h2138, h2313, hlam]
                                          · rcases p2300_3 (m.d 2 5) (by simp) with h2315 | h2315
                                            · rcases p2300_3 (m.d 3 5) (by simp) with h2316 | h2316
                                              · rcases p2300_3 (m.d 4 5) (by simp) with h2317 | h2317
                                                · linarith only [h2260, h2317, hlam]
                                                · linarith only [h1898, h2317, hlam]
                                              · linarith only [h1790, h2316, hlam]
                                            · linarith only [h2315, h947, hlam]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        rcases p2300_3 (m.d 0 5) (by simp) with h2322 | h2322
                                        · linarith only [h2322, h947, hlam]
                                        · linarith only [h2322, h3, hlam]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h2258, hlam, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h0, h1183, h1898, h4, hc12, hc25, hlam, hphi, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        rcases p2300_3 (m.d 0 5) (by simp) with h2328 | h2328
                                        · linarith only [h1790, h2328, hlam]
                                        · rcases p2300_3 (m.d 1 5) (by simp) with h2330 | h2330
                                          · linarith only [h2142, h2330, hlam]
                                          · rcases p2300_3 (m.d 2 5) (by simp) with h2332 | h2332
                                            · linarith only [h2258, h2332, hlam]
                                            · linarith only [h2332, h947, hlam]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        rcases p2300_3 (m.d 0 5) (by simp) with h2335 | h2335
                                        · linarith only [h1790, h2335, hlam]
                                        · linarith only [h2335, h3, hlam]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h0, h2261, h947, hc12, hc34, hlam, hphi, ht23, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h0, h1183, h1898, h2261, h4, hc12, hc34, hlam, hphi, ht23, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h0, h1183, h1898, h2146, h2260, h4, hc12, hc34, hlam, hphi, ht23, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h2130, h2140, h2144, h2146, h2260, hc12, hc34, hlam, hphi, ht23, p2300_1]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h2260, hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [h2261, hlam, p2300_0]
                                      · have p2300_0 := h2300c.1
                                        have p2300_1 := h2300c.2.1
                                        have p2300_2 := h2300c.2.2.1
                                        have p2300_3 := h2300c.2.2.2
                                        linarith only [hlam, p2300_0]
                            · linarith only [h2291, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h0, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h2130, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h2132, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h2138, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h1, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2262_1, u1elo0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h2140, hlam, p2262_1]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h2142, hlam, p2262_1]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h2, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h1898, h2, h2146, h2260, hc12, hc34, hlam, hphi, ht23, p2262_1]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h1898, h2, h2146, h2260, hc13, hc34, hlam, hphi, p2262_1]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h2144, hlam, p2262_1]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h3, hlam, p2262_0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2262_1, u1elo0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h2130, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2262_1, u1elo0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2262_1, u1elo0]
                          · have p2262_0 := h2262c.1
                            have p2262_1 := h2262c.2.1
                            have p2262_2 := h2262c.2.2.1
                            have p2262_3 := h2262c.2.2.2
                            linarith only [hlam, p2262_0]
                        · linarith only [h2146, h2260, h2261, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2368 | h2368
                        · linarith only [h0, h2146, h2260, h2368, h4, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h2146, h2368, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h947 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h1183 | h1183
  · exact r1l7_21_15_M_LI_L_I_s1_x0_x0_x1_x1_x0 m hb1 hb5 hg0 hg1 h2 h3 h4 h947 h1183
  · exact r1l7_21_15_M_LI_L_I_s1_x0_x0_x1_x1_x1 m hb1 hb5 hg0 hg1 h2 h3 h4 h947 h1183

set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h947 | h947
  · exact r1l7_21_15_M_LI_L_I_s1_x0_x0_x1_x0 m hb1 hb5 hg0 hg1 h2 h3 h4 h947
  · exact r1l7_21_15_M_LI_L_I_s1_x0_x0_x1_x1 m hb1 hb5 hg0 hg1 h2 h3 h4 h947

set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_15_M_LI_L_I_s1_x0_x0_x0 m hb1 hb5 hg0 hg1 h2 h3 h4
  · exact r1l7_21_15_M_LI_L_I_s1_x0_x0_x1 m hb1 hb5 hg0 hg1 h2 h3 h4

set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 3 (by decide) (by decide) with h2371 | h2371
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2372 | h2372
    · linarith only [h0, h2372, h3, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2374 | h2374
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2375 | h2375
        · linarith only [h1, h2375, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2377 | h2377
          · linarith only [h0, h2371, h2374, h2377, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2379 | h2379
            · linarith only [h0, h2379, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
            · linarith only [h0, h2371, h2379, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2382 | h2382
        · linarith only [h0, h2371, h2382, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2384 | h2384
          · linarith only [h2, h2384, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2386 | h2386
            · linarith only [h0, h2386, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
            · linarith only [h0, h2371, h2386, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2389 | h2389
    · linarith only [h1, h2371, h2389, h3, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2391 | h2391
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2392 | h2392
        · linarith only [h1, h2392, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2394 | h2394
          · linarith only [h1, h2391, h2394, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2396 | h2396
            · linarith only [h0, h2371, h2396, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2398 | h2398
              · linarith only [h0, h2398, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2400 | h2400
                · linarith only [h1, h2389, h2396, h2400, h3, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2402 | h2402
                  · linarith only [h1, h2402, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                  · linarith only [h1, h2391, h2396, h2402, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2405 | h2405
        · linarith only [h2, h2391, h2405, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2407 | h2407
          · linarith only [h2, h2407, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2409 | h2409
            · linarith only [h0, h2371, h2409, h3, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2411 | h2411
              · linarith only [h0, h2411, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2413 | h2413
                · linarith only [h1, h2409, h2413, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2415 | h2415
                  · linarith only [h1, h2371, h2391, h2415, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2417 | h2417
                    · linarith only [h1, h2405, h2417, h3, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2419 | h2419
                      · linarith only [h2, h2407, h2419, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2421 | h2421
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2422 | h2422
                          · linarith only [h0, h2417, h2422, h3, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h2371, h2391, h2421, h2422, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2425 | h2425
                          · linarith only [h0, h2371, h2405, h2421, h2425, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2427 | h2427
                            · linarith only [h2, h2409, h2415, h2419, h2427, h3, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2429 | h2429
                              · linarith only [h0, h2371, h2421, h2427, h2429, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h2371, h2421, h2429, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_15_M_LI_L_I_s1_x0_x0 m hb1 hb5 hg0 hg1 h2 h3
  · exact r1l7_21_15_M_LI_L_I_s1_x0_x1 m hb1 hb5 hg0 hg1 h2 h3

set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 5 (by decide) (by decide) with h2432 | h2432
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2433 | h2433
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2434 | h2434
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2435 | h2435
        · linarith only [h1, h2, h2435, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2437 | h2437
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2438 | h2438
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2439 | h2439
              · linarith only [h0, h2, h2439, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · linarith only [h0, h2, h2433, h2439, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · linarith only [h0, h2, h2433, h2437, h2438, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2443 | h2443
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2444 | h2444
              · linarith only [h0, h2, h2444, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · linarith only [h0, h2, h2433, h2444, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · linarith only [h0, h2, h2434, h2443, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2448 | h2448
        · linarith only [h1, h2, h2448, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2450 | h2450
          · linarith only [h2433, h2434, h2450, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2452 | h2452
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2453 | h2453
              · linarith only [h0, h2, h2453, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · linarith only [h2, h2432, h2433, h2434, h2453, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · linarith only [h2, h2432, h2452, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2457 | h2457
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2458 | h2458
        · linarith only [h1, h2, h2458, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2460 | h2460
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2461 | h2461
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2462 | h2462
              · linarith only [h2433, h2457, h2462, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2464 | h2464
                · linarith only [h0, h2, h2464, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2466 | h2466
                  · linarith only [h1, h2, h2462, h2466, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                  · linarith only [h2433, h2457, h2466, hc12, hc23, hlam, hphi]
            · linarith only [h1, h2, h2433, h2457, h2461, hlam]
          · linarith only [h2433, h2457, h2460, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2471 | h2471
        · linarith only [h1, h2, h2471, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2473 | h2473
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2474 | h2474
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2475 | h2475
              · linarith only [h0, h2, h2433, h2475, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2477 | h2477
                · linarith only [h0, h2, h2477, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2479 | h2479
                  · linarith only [h0, h2457, h2479, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2481 | h2481
                    · linarith only [h1, h2, h2471, h2481, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2483 | h2483
                      · linarith only [h1, h2, h2483, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · linarith only [h1, h2, h2473, h2475, h2483, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · linarith only [h1, h2, h2473, h2474, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2487 | h2487
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2488 | h2488
              · linarith only [h0, h2, h2433, h2488, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2490 | h2490
                · linarith only [h0, h2, h2490, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2492 | h2492
                  · linarith only [h1, h2, h2457, h2488, h2492, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2494 | h2494
                    · linarith only [h1, h2, h2471, h2494, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2496 | h2496
                      · linarith only [h1, h2473, h2496, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2498 | h2498
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2499 | h2499
                          · linarith only [h0, h2, h2494, h2499, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2501 | h2501
                            · linarith only [h0, h2433, h2473, h2499, h2501, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2503 | h2503
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2504 | h2504
                                · rcases h1bigk with h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c | h2505c
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2505_1, u1elo3]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2, h2488, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2505_1, u1elo3]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2, hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p2505_1, u1elo3]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h0, hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2488, hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2490, hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2492, hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h1, hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h1, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2505_1, u1elo3]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2494, hlam, p2505_1]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2496, hlam, p2505_1]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [hc01, hlam, hphi, p2505_1, u1elo3]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    rcases p2505_3 (m.d 0 1) (by simp) with h2522 | h2522
                                    · linarith only [h2, h2522, hlam]
                                    · linarith only [h0, h2522, hlam]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    rcases p2505_3 (m.d 0 1) (by simp) with h2525 | h2525
                                    · linarith only [h2, h2525, hlam]
                                    · linarith only [h1, h2525, hlam]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    rcases p2505_3 (m.d 0 1) (by simp) with h2529 | h2529
                                    · linarith only [h2, h2529, hlam]
                                    · linarith only [h2432, h2529, hlam]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2432, hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2432, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2505_1, u1elo0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2, h2432, h2488, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2505_1, u1elo3]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [h2498, hlam, p2505_0]
                                  · have p2505_0 := h2505c.1
                                    have p2505_1 := h2505c.2.1
                                    have p2505_2 := h2505c.2.2.1
                                    have p2505_3 := h2505c.2.2.2
                                    linarith only [hlam, p2505_0]
                                · linarith only [h0, h2, h2433, h2471, h2487, h2504, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                              · linarith only [h2, h2432, h2490, h2498, h2503, hlam]
                        · linarith only [h0, h2, h2498, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h2, h2432, h2487, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2541 | h2541
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2542 | h2542
      · linarith only [h0, h2432, h2542, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2544 | h2544
        · linarith only [h1, h2, h2544, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2546 | h2546
          · linarith only [h0, h2432, h2541, h2546, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2548 | h2548
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2549 | h2549
              · linarith only [h0, h2, h2549, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · linarith only [h0, h2, h2541, h2549, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2552 | h2552
              · linarith only [h0, h2, h2552, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · linarith only [h0, h2, h2541, h2552, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2555 | h2555
      · linarith only [h1, h2432, h2541, h2555, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2557 | h2557
        · linarith only [h1, h2, h2557, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2559 | h2559
          · linarith only [h1, h2432, h2559, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2561 | h2561
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2562 | h2562
              · linarith only [h0, h2, h2541, h2562, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2564 | h2564
                · linarith only [h0, h2, h2564, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2566 | h2566
                  · linarith only [h1, h2432, h2555, h2562, h2566, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2568 | h2568
                    · linarith only [h1, h2, h2557, h2568, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2570 | h2570
                      · linarith only [h1, h2432, h2559, h2570, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2572 | h2572
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2573 | h2573
                          · linarith only [h1, h2432, h2562, h2568, h2572, h2573, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2575 | h2575
                            · linarith only [h1, h2432, h2562, h2570, h2573, h2575, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2577 | h2577
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2578 | h2578
                                · rcases h1bigk with h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c | h2579c
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2432, h2572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2579_1, u1elo3]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2432, h2562, h2572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2579_1, u1elo3]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2, hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2432, hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h0, hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2562, hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2564, hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2566, hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h1, hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h1, h2432, h2572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2579_1, u1elo3]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2568, hlam, p2579_1]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2570, hlam, p2579_1]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [hc01, hlam, hphi, p2579_1, u1elo3]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    rcases p2579_3 (m.d 0 1) (by simp) with h2596 | h2596
                                    · linarith only [h2, h2596, hlam]
                                    · linarith only [h0, h2596, hlam]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    rcases p2579_3 (m.d 0 1) (by simp) with h2599 | h2599
                                    · linarith only [h2, h2599, hlam]
                                    · linarith only [h1, h2599, hlam]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h1, h2432, h2562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2579_1, u1elo3]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h1, h2562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2579_1, u1elo4]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    rcases p2579_3 (m.d 0 1) (by simp) with h2605 | h2605
                                    · linarith only [h2432, h2605, hlam]
                                    · linarith only [h0, h2605, hlam]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    rcases p2579_3 (m.d 0 1) (by simp) with h2608 | h2608
                                    · linarith only [h2432, h2608, hlam]
                                    · linarith only [h1, h2608, hlam]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [h2572, hlam, p2579_0]
                                  · have p2579_0 := h2579c.1
                                    have p2579_1 := h2579c.2.1
                                    have p2579_2 := h2579c.2.2.1
                                    have p2579_3 := h2579c.2.2.2
                                    linarith only [hlam, p2579_0]
                                · linarith only [h0, h2, h2541, h2557, h2561, h2578, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                              · linarith only [h1, h2, h2562, h2564, h2577, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1, h2, h2561, h2562, h2572, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2616 | h2616
              · linarith only [h0, h2541, h2616, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2618 | h2618
                · linarith only [h0, h2432, h2618, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2620 | h2620
                  · linarith only [h1, h2432, h2555, h2616, h2620, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2622 | h2622
                    · linarith only [h1, h2432, h2541, h2557, h2622, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2624 | h2624
                      · linarith only [h1, h2, h2559, h2561, h2624, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2626 | h2626
                        · linarith only [h2, h2561, h2626, hc01, hlam, hphi, u1elo3]
                        · linarith only [h1, h2, h2616, h2626, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
