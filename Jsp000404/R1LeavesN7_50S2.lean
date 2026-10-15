import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_50S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5456000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1107 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1763 | h1763
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1764 | h1764
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1765 | h1765
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1766 | h1766
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1767 | h1767
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1768 | h1768
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1769 | h1769
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1770 | h1770
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1771 | h1771
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1772 | h1772
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1773 | h1773
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1774 | h1774
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1775 | h1775
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1776 | h1776
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1777 | h1777
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1778 | h1778
                                · linarith only [h1763, h1775, h1778, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h0emin with h1780 | h1780 | h1780 | h1780 | h1780
                                  · linarith only [h1107, h1774, h1780, hc14, hlam, ht01]
                                  · rcases h2bigk with h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h0, hlam, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h0, h1775, h1777, h1778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h0, h1777, h1778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      rcases p1782_3 (m.d 0 2) (by simp) with h1787 | h1787
                                      · rcases p1782_3 (m.d 1 2) (by simp) with h1788 | h1788
                                        · rcases p1782_3 (m.d 2 3) (by simp) with h1789 | h1789
                                          · linarith only [h1763, h1789, hlam]
                                          · linarith only [h1776, h1789, hlam]
                                        · linarith only [h1771, h1788, hlam]
                                      · linarith only [h1787, hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1780, hc12, hlam, ht01, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1775, h1777, h1778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1777, h1778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      rcases p1782_3 (m.d 0 2) (by simp) with h1798 | h1798
                                      · linarith only [h0, h1798, hlam]
                                      · linarith only [h1765, h1798, hlam]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1763, hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1769, hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1763, h1777, h1778, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1763, h1777, h1778, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1782_1, u3elo0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1764, hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1770, hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1775, hlam, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h0, h1764, h1777, h1778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1765, hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1771, hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1776, hlam, p1782_1]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [h1777, hlam, p1782_0]
                                    · have p1782_0 := h1782c.1
                                      have p1782_1 := h1782c.2.1
                                      have p1782_2 := h1782c.2.2.1
                                      have p1782_3 := h1782c.2.2.2
                                      linarith only [hlam, p1782_0]
                                  · linarith only [h1780, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1766, h1780, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1107, h1772, h1774, h1780, hlam, ht01, ht12, ht23, u3elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1819 | h1819
                                · linarith only [h1766, h1777, h1819, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                · rcases h0emin with h1821 | h1821 | h1821 | h1821 | h1821
                                  · linarith only [h1107, h1772, h1774, h1821, hlam, ht01, ht12, ht23, u3elo1]
                                  · rcases h2bigk with h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h0, hlam, p1823_1]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h0, h1776, hc12, hlam, hphi, ht01, ht0b, ht5b, p1823_1, u5ehi3]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      rcases p1823_3 (m.d 0 2) (by simp) with h1827 | h1827
                                      · rcases p1823_3 (m.d 1 2) (by simp) with h1828 | h1828
                                        · rcases p1823_3 (m.d 2 3) (by simp) with h1829 | h1829
                                          · linarith only [h1763, h1829, hlam]
                                          · linarith only [h1775, h1829, hlam]
                                        · linarith only [h1770, h1828, hlam]
                                      · linarith only [h1827, hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      rcases p1823_3 (m.d 0 2) (by simp) with h1834 | h1834
                                      · rcases p1823_3 (m.d 1 2) (by simp) with h1835 | h1835
                                        · rcases p1823_3 (m.d 2 3) (by simp) with h1836 | h1836
                                          · linarith only [h1763, h1836, hlam]
                                          · linarith only [h1776, h1836, hlam]
                                        · linarith only [h1771, h1835, hlam]
                                      · linarith only [h1834, hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1821, hc12, hlam, ht01, p1823_1]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1776, hc12, hlam, hphi, ht01, ht0b, ht5b, p1823_1, u5ehi3]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      rcases p1823_3 (m.d 0 2) (by simp) with h1844 | h1844
                                      · linarith only [h0, h1844, hlam]
                                      · linarith only [h1764, h1844, hlam]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      rcases p1823_3 (m.d 0 2) (by simp) with h1847 | h1847
                                      · linarith only [h0, h1847, hlam]
                                      · linarith only [h1765, h1847, hlam]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1763, hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1769, hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      rcases p1823_3 (m.d 0 2) (by simp) with h1853 | h1853
                                      · rcases p1823_3 (m.d 1 2) (by simp) with h1854 | h1854
                                        · rcases p1823_3 (m.d 2 3) (by simp) with h1855 | h1855
                                          · rcases p1823_3 (m.d 2 4) (by simp) with h1856 | h1856
                                            · linarith only [h1775, h1856, hlam]
                                            · rcases p1823_3 (m.d 2 5) (by simp) with h1858 | h1858
                                              · linarith only [h1776, h1858, hlam]
                                              · linarith only [h1777, h1858, hlam]
                                          · linarith only [h1775, h1855, hlam]
                                        · linarith only [h1770, h1854, hlam]
                                      · linarith only [h1764, h1853, hlam]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1763, hc02, hlam, hphi, ht0b, ht5b, p1823_1, u5ehi2]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1764, hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1770, hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1775, hlam, p1823_1]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1777, hlam, p1823_1]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1765, hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1771, hlam, p1823_0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1776, hlam, p1823_1]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [h1766, h1768, h1775, h1777, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1823_1, u3elo0]
                                    · have p1823_0 := h1823c.1
                                      have p1823_1 := h1823c.2.1
                                      have p1823_2 := h1823c.2.2.1
                                      have p1823_3 := h1823c.2.2.2
                                      linarith only [hlam, p1823_0]
                                  · linarith only [h1821, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1766, h1821, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1107, h1772, h1774, h1821, hlam, ht01, ht12, ht23, u3elo1]
                            · linarith only [h1767, h1776, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1766, h1775, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1107, h1766, h1768, h1774, hc01, hlam, hphi, ht12, ht23, u3elo0]
                      · linarith only [h1767, h1773, hc13, hlam, hphi, u3elo0]
                    · linarith only [h1766, h1769, h1772, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h1765, h1771, hlam]
                · linarith only [h0, h1764, h1770, hlam]
              · linarith only [h0, h1765, h1769, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1886 | h1886
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1887 | h1887
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1888 | h1888
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1889 | h1889
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1890 | h1890
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1891 | h1891
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1892 | h1892
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1893 | h1893
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1894 | h1894
                              · linarith only [h1764, h1768, h1894, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1896 | h1896
                                · linarith only [h1764, h1768, h1892, h1896, hlam]
                                · rcases h0emin with h1898 | h1898 | h1898 | h1898 | h1898
                                  · linarith only [h0, h1898, hc12, hlam, ht01]
                                  · rcases h2bigk with h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h0, hlam, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1893, hc02, hlam, hphi, ht0b, ht5b, p1900_1, u5ehi3]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      rcases p1900_3 (m.d 0 2) (by simp) with h1904 | h1904
                                      · rcases p1900_3 (m.d 1 2) (by simp) with h1905 | h1905
                                        · rcases p1900_3 (m.d 2 3) (by simp) with h1906 | h1906
                                          · linarith only [h1763, h1906, hlam]
                                          · linarith only [h1892, h1906, hlam]
                                        · linarith only [h1887, h1905, hlam]
                                      · linarith only [h1904, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      rcases p1900_3 (m.d 0 2) (by simp) with h1911 | h1911
                                      · rcases p1900_3 (m.d 1 2) (by simp) with h1912 | h1912
                                        · rcases p1900_3 (m.d 2 3) (by simp) with h1913 | h1913
                                          · linarith only [h1763, h1913, hlam]
                                          · linarith only [h1893, h1913, hlam]
                                        · linarith only [h1888, h1912, hlam]
                                      · linarith only [h1911, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1898, hc12, hlam, ht01, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1893, hc12, hlam, hphi, ht01, ht0b, ht5b, p1900_1, u5ehi3]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      rcases p1900_3 (m.d 0 2) (by simp) with h1921 | h1921
                                      · linarith only [h0, h1921, hlam]
                                      · linarith only [h1764, h1921, hlam]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      rcases p1900_3 (m.d 0 2) (by simp) with h1924 | h1924
                                      · linarith only [h0, h1924, hlam]
                                      · linarith only [h1765, h1924, hlam]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1763, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1886, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      rcases p1900_3 (m.d 0 2) (by simp) with h1930 | h1930
                                      · rcases p1900_3 (m.d 1 2) (by simp) with h1931 | h1931
                                        · rcases p1900_3 (m.d 2 3) (by simp) with h1932 | h1932
                                          · rcases p1900_3 (m.d 2 4) (by simp) with h1933 | h1933
                                            · linarith only [h1892, h1933, hlam]
                                            · rcases p1900_3 (m.d 2 5) (by simp) with h1935 | h1935
                                              · linarith only [h1893, h1935, hlam]
                                              · linarith only [h1894, h1935, hlam]
                                          · linarith only [h1892, h1932, hlam]
                                        · linarith only [h1887, h1931, hlam]
                                      · linarith only [h1764, h1930, hlam]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1763, h1893, hc02, hlam, hphi, ht0b, ht5b, p1900_1, u5ehi3]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1764, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1887, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1892, hlam, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1894, hlam, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1765, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1888, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1893, hlam, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1765, h1768, h1889, h1891, h1892, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1900_1, u3elo1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                  · linarith only [h1898, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1766, h1898, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1768, h1889, h1891, h1898, hlam, ht01, ht12, ht23, u3elo1]
                            · linarith only [h1767, h1893, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1766, h1892, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1957 | h1957
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1958 | h1958
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1959 | h1959
                              · linarith only [h0, h1107, h1764, h1891, h1959, hc01, hc12, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1961 | h1961
                                · linarith only [h1107, h1891, h1961, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                · rcases h0emin with h1963 | h1963 | h1963 | h1963 | h1963
                                  · linarith only [h1107, h1963, hc15, hlam, ht01]
                                  · rcases h2bigk with h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c | h1965c
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h0, hlam, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h0, h1958, hc12, hlam, hphi, ht01, ht0b, ht5b, p1965_1, u5ehi3]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h1969 | h1969
                                      · rcases p1965_3 (m.d 1 2) (by simp) with h1970 | h1970
                                        · rcases p1965_3 (m.d 2 3) (by simp) with h1971 | h1971
                                          · linarith only [h1763, h1971, hlam]
                                          · linarith only [h1957, h1971, hlam]
                                        · linarith only [h1887, h1970, hlam]
                                      · linarith only [h1969, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h1976 | h1976
                                      · rcases p1965_3 (m.d 1 2) (by simp) with h1977 | h1977
                                        · rcases p1965_3 (m.d 2 3) (by simp) with h1978 | h1978
                                          · linarith only [h1763, h1978, hlam]
                                          · linarith only [h1958, h1978, hlam]
                                        · linarith only [h1888, h1977, hlam]
                                      · linarith only [h1976, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1963, hc12, hlam, ht01, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1958, hc12, hlam, hphi, ht01, ht0b, ht5b, p1965_1, u5ehi3]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h1986 | h1986
                                      · linarith only [h0, h1986, hlam]
                                      · linarith only [h1764, h1986, hlam]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h1989 | h1989
                                      · linarith only [h0, h1989, hlam]
                                      · linarith only [h1765, h1989, hlam]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1763, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1886, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h1995 | h1995
                                      · rcases p1965_3 (m.d 1 2) (by simp) with h1996 | h1996
                                        · rcases p1965_3 (m.d 2 3) (by simp) with h1997 | h1997
                                          · rcases p1965_3 (m.d 2 4) (by simp) with h1998 | h1998
                                            · linarith only [h1957, h1998, hlam]
                                            · rcases p1965_3 (m.d 2 5) (by simp) with h2000 | h2000
                                              · linarith only [h1958, h2000, hlam]
                                              · linarith only [h1959, h2000, hlam]
                                          · linarith only [h1957, h1997, hlam]
                                        · linarith only [h1887, h1996, hlam]
                                      · linarith only [h1764, h1995, hlam]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1763, h1958, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1965_1, u3elo0, u5ehi3]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1764, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1887, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1957, hlam, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1959, hlam, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1765, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1888, hlam, p1965_0]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [h1958, hlam, p1965_1]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      rcases p1965_3 (m.d 0 2) (by simp) with h2015 | h2015
                                      · rcases p1965_3 (m.d 1 2) (by simp) with h2016 | h2016
                                        · rcases p1965_3 (m.d 2 3) (by simp) with h2017 | h2017
                                          · rcases p1965_3 (m.d 2 4) (by simp) with h2018 | h2018
                                            · linarith only [h1959, h2018, hlam]
                                            · rcases p1965_3 (m.d 2 5) (by simp) with h2020 | h2020
                                              · rcases h2emin with h2021 | h2021 | h2021 | h2021 | h2021
                                                · rcases h5bigk with h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [hlam, p2022_0]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1107, hlam, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1107, h1890, h1957, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1965_1, p2022_1, u3elo1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1107, h1890, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2022_1, u3elo1, u5ehi3]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1768, hlam, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1890, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2022_1, u3elo1, u5ehi0]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [hlam, p2022_0]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1890, h1957, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1965_1, p2022_1, u3elo1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1890, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2022_1, u3elo1, u5ehi3]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1891, hlam, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1765, hlam, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1888, hlam, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [hlam, p2022_0]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1107, h1765, h1890, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2022_1, u3elo1, u5ehi3]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1959, hlam, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1767, hlam, p2022_0]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1890, hlam, p2022_0]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1958, hlam, p2022_0]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [hlam, p2022_0]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1961, hlam, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1765, h1957, hc34, hc45, hlam, hphi, p1965_1, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1107, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [h1957, hc34, hc45, hlam, hphi, p1965_1, p2022_1]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    rcases p2022_3 (m.d 0 5) (by simp) with h2046 | h2046
                                                    · linarith only [h1768, h2046, hlam]
                                                    · linarith only [h1767, h2046, hlam]
                                                  · have p2022_0 := h2022c.1
                                                    have p2022_1 := h2022c.2.1
                                                    have p2022_2 := h2022c.2.2.1
                                                    have p2022_3 := h2022c.2.2.2
                                                    linarith only [hlam, p2022_0]
                                                · rcases h5bigk with h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c | h2050c
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [hlam, p2050_0]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1107, hlam, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1107, h1890, h1957, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1965_1, p2050_1, u3elo1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1107, h1890, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2050_1, u3elo1, u5ehi3]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1768, hlam, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1890, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2050_1, u3elo1, u5ehi0]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [hlam, p2050_0]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1890, h1957, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1965_1, p2050_1, u3elo1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1890, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2050_1, u3elo1, u5ehi3]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1891, hlam, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1765, hlam, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1888, hlam, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [hlam, p2050_0]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1763, h1958, hc02, hlam, hphi, ht0b, ht5b, p2050_1, u5ehi3]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1959, hlam, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1767, hlam, p2050_0]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1890, hlam, p2050_0]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1958, hlam, p2050_0]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [hlam, p2050_0]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1961, hlam, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1765, h1957, hc34, hc45, hlam, hphi, p1965_1, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1107, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [h1957, hc34, hc45, hlam, hphi, p1965_1, p2050_1]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    rcases p2050_3 (m.d 0 5) (by simp) with h2074 | h2074
                                                    · linarith only [h1768, h2074, hlam]
                                                    · linarith only [h1767, h2074, hlam]
                                                  · have p2050_0 := h2050c.1
                                                    have p2050_1 := h2050c.2.1
                                                    have p2050_2 := h2050c.2.2.1
                                                    have p2050_3 := h2050c.2.2.2
                                                    linarith only [hlam, p2050_0]
                                                · linarith only [h1763, h2021, hlam, ht23, u3elo0]
                                                · linarith only [h1107, h1765, h1890, h2021, hlam, ht23, p1965_1, u3elo1]
                                                · linarith only [h1107, h1765, h1890, h2021, hlam, ht23, u3elo1]
                                              · linarith only [h1959, h2020, hlam]
                                          · linarith only [h1957, h2017, hlam]
                                        · linarith only [h1887, h2016, hlam]
                                      · linarith only [h1764, h2015, hlam]
                                    · have p1965_0 := h1965c.1
                                      have p1965_1 := h1965c.2.1
                                      have p1965_2 := h1965c.2.2.1
                                      have p1965_3 := h1965c.2.2.2
                                      linarith only [hlam, p1965_0]
                                  · linarith only [h1963, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1768, h1963, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h1107, h1890, h1963, hlam, ht01, ht12, ht23, u3elo1]
                            · linarith only [h1767, h1958, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1766, h1957, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1767, h1890, hc13, hlam, hphi, u3elo0]
                    · linarith only [h1766, h1886, h1889, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h1765, h1888, hlam]
                · linarith only [h0, h1764, h1887, hlam]
              · linarith only [h0, h1763, h1767, h1886, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2096 | h2096
            · linarith only [h1766, h1767, h2096, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2098 | h2098
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2099 | h2099
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2100 | h2100
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2101 | h2101
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2102 | h2102
                      · linarith only [h1767, h2102, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2104 | h2104
                        · linarith only [h2096, h2101, h2102, h2104, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2106 | h2106
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2107 | h2107
                            · linarith only [h1763, h2102, h2107, hc13, hlam, hphi, u3elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2109 | h2109
                              · linarith only [h1764, h1766, h1767, h2104, h2109, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2111 | h2111
                                · linarith only [h1766, h1767, h2096, h2111, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · rcases h0emin with h2113 | h2113 | h2113 | h2113 | h2113
                                  · linarith only [h0, h2113, hc12, hlam, ht01]
                                  · rcases h2bigk with h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h0, hlam, p2115_1]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 2) (by simp) with h2118 | h2118
                                      · rcases p2115_3 (m.d 1 2) (by simp) with h2119 | h2119
                                        · rcases p2115_3 (m.d 2 3) (by simp) with h2120 | h2120
                                          · linarith only [h2120, hlam, p2115_0]
                                          · rcases p2115_3 (m.d 2 4) (by simp) with h2122 | h2122
                                            · linarith only [h1764, h2122, hlam]
                                            · rcases p2115_3 (m.d 2 5) (by simp) with h2124 | h2124
                                              · linarith only [h1765, h2124, hlam]
                                              · linarith only [h2107, h2124, hlam]
                                        · linarith only [h2098, h2119, hlam]
                                      · linarith only [h2118, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 2) (by simp) with h2129 | h2129
                                      · rcases p2115_3 (m.d 1 2) (by simp) with h2130 | h2130
                                        · rcases p2115_3 (m.d 2 3) (by simp) with h2131 | h2131
                                          · linarith only [h1763, h2131, hlam]
                                          · linarith only [h2106, h2131, hlam]
                                        · linarith only [h2099, h2130, hlam]
                                      · linarith only [h2129, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 2) (by simp) with h2136 | h2136
                                      · rcases p2115_3 (m.d 1 2) (by simp) with h2137 | h2137
                                        · rcases p2115_3 (m.d 2 3) (by simp) with h2138 | h2138
                                          · linarith only [h1763, h2138, hlam]
                                          · rcases p2115_3 (m.d 2 4) (by simp) with h2140 | h2140
                                            · linarith only [h1764, h2140, hlam]
                                            · rcases p2115_3 (m.d 2 5) (by simp) with h2142 | h2142
                                              · linarith only [h2142, hlam, p2115_0]
                                              · rcases h2emin with h2144 | h2144 | h2144 | h2144 | h2144
                                                · rcases h5bigk with h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c | h2145c
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [hlam, p2145_0]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1107, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1767, h2106, h2107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2145_1, u3elo4]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1767, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2096, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1107, h2102, hc01, hlam, hphi, ht12, ht23, p2145_1, u3elo4]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [hlam, p2145_0]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2102, h2106, h2107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2145_1, u3elo4]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2102, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2104, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1765, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2100, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [hlam, p2145_0]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2107, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2109, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1765, h2106, h2107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2145_1, u3elo4]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2145_1, u3elo4, u5ehi1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2106, h2107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2145_1, u3elo4]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [hlam, p2145_0]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2111, hlam, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1765, h2106, h2107, hc34, hc45, hlam, hphi, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1107, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h2106, h2107, hc34, hc45, hlam, hphi, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [h1763, h1767, h2106, hc34, hc45, hlam, hphi, p2145_1]
                                                  · have p2145_0 := h2145c.1
                                                    have p2145_1 := h2145c.2.1
                                                    have p2145_2 := h2145c.2.2.1
                                                    have p2145_3 := h2145c.2.2.2
                                                    linarith only [hlam, p2145_0]
                                                · rcases h5bigk with h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [hlam, p2171_0]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h1107, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h1767, h2106, h2107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2171_1, u3elo4]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h1767, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2096, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2102, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2171_1, u3elo4, u5ehi0]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [hlam, p2171_0]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2102, h2106, h2107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2171_1, u3elo4]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2102, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2104, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h1765, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2100, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [hlam, p2171_0]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2107, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2109, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h1765, h2106, h2107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2171_1, u3elo4]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2171_1, u3elo4, u5ehi1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2106, h2107, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2171_1, u3elo4]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [hlam, p2171_0]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2111, hlam, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h1765, h2106, h2107, hc34, hc45, hlam, hphi, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h1107, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h2106, h2107, hc34, hc45, hlam, hphi, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [h1763, h1767, h2106, hc34, hc45, hlam, hphi, p2171_1]
                                                  · have p2171_0 := h2171c.1
                                                    have p2171_1 := h2171c.2.1
                                                    have p2171_2 := h2171c.2.2.1
                                                    have p2171_3 := h2171c.2.2.2
                                                    linarith only [hlam, p2171_0]
                                                · linarith only [h1763, h1767, h2144, hlam, ht23, u3elo4]
                                                · linarith only [h1764, h1766, h1767, h2144, hlam, ht23, u3elo4]
                                                · linarith only [h0, h1763, h1767, h2106, h2144, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p2115_1, u3elo4]
                                        · linarith only [h2100, h2137, hlam]
                                      · linarith only [h2136, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2113, hc12, hlam, ht01, p2115_1]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 2) (by simp) with h2204 | h2204
                                      · linarith only [h0, h2204, hlam]
                                      · linarith only [h1763, h2204, hlam]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 2) (by simp) with h2207 | h2207
                                      · linarith only [h0, h2207, hlam]
                                      · linarith only [h1764, h2207, hlam]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 2) (by simp) with h2210 | h2210
                                      · linarith only [h0, h2210, hlam]
                                      · linarith only [h1765, h2210, hlam]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1763, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2098, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1763, h1767, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2115_1, u3elo4]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2107, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1764, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2099, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2106, hlam, p2115_1]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2109, hlam, p2115_1]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1765, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2100, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1765, h2106, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2115_1]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 2) (by simp) with h2226 | h2226
                                      · rcases p2115_3 (m.d 1 2) (by simp) with h2227 | h2227
                                        · rcases p2115_3 (m.d 2 3) (by simp) with h2228 | h2228
                                          · linarith only [h2107, h2228, hlam]
                                          · linarith only [h2106, h2228, hlam]
                                        · linarith only [h2099, h2227, hlam]
                                      · linarith only [h1764, h2226, hlam]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                  · linarith only [h2113, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1766, h2113, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1107, h2102, h2113, hlam, ht01, ht12, ht23, u3elo4]
                          · linarith only [h2101, h2106, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1766, h1767, h2101, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h1765, h2100, hlam]
                · linarith only [h0, h1764, h2099, hlam]
              · linarith only [h0, h1765, h2098, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2242 | h2242
          · linarith only [h1766, h2242, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2244 | h2244
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2245 | h2245
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2246 | h2246
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2247 | h2247
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2248 | h2248
                    · linarith only [h1766, h2248, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2250 | h2250
                      · linarith only [h2242, h2248, h2250, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2252 | h2252
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2253 | h2253
                          · linarith only [h1763, h2248, h2253, hc13, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2255 | h2255
                            · linarith only [h2242, h2245, h2255, hc03, hlam, hphi, u3elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2257 | h2257
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2258 | h2258
                                · rcases h0emin with h2259 | h2259 | h2259 | h2259 | h2259
                                  · linarith only [h0, h2259, hc12, hlam, ht01]
                                  · rcases h2bigk with h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c | h2261c
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h0, hlam, p2261_1]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      rcases p2261_3 (m.d 0 2) (by simp) with h2264 | h2264
                                      · rcases p2261_3 (m.d 1 2) (by simp) with h2265 | h2265
                                        · rcases p2261_3 (m.d 2 3) (by simp) with h2266 | h2266
                                          · linarith only [h2266, hlam, p2261_0]
                                          · rcases p2261_3 (m.d 2 4) (by simp) with h2268 | h2268
                                            · linarith only [h1764, h2268, hlam]
                                            · linarith only [h2253, h2268, hlam]
                                        · linarith only [h2245, h2265, hlam]
                                      · linarith only [h2264, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2257, hc02, hlam, hphi, ht0b, ht5b, p2261_1, u5ehi4]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      rcases p2261_3 (m.d 0 2) (by simp) with h2274 | h2274
                                      · rcases p2261_3 (m.d 1 2) (by simp) with h2275 | h2275
                                        · rcases p2261_3 (m.d 2 3) (by simp) with h2276 | h2276
                                          · linarith only [h1763, h2276, hlam]
                                          · rcases p2261_3 (m.d 2 4) (by simp) with h2278 | h2278
                                            · linarith only [h1764, h2278, hlam]
                                            · linarith only [h2257, h2278, hlam]
                                        · linarith only [h2247, h2275, hlam]
                                      · linarith only [h2274, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2259, hc12, hlam, ht01, p2261_1]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      rcases p2261_3 (m.d 0 2) (by simp) with h2285 | h2285
                                      · linarith only [h0, h2285, hlam]
                                      · linarith only [h1763, h2285, hlam]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2257, hc12, hlam, hphi, ht01, ht0b, ht5b, p2261_1, u5ehi4]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      rcases p2261_3 (m.d 0 2) (by simp) with h2289 | h2289
                                      · linarith only [h0, h2289, hlam]
                                      · linarith only [h1765, h2289, hlam]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h1763, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2245, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2253, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2255, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h1764, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2246, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h1764, h1766, hc23, hlam, hphi, p2261_1, u3elo3]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h1764, h1766, h2257, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2261_1, u3elo3, u5ehi4]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h1765, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2247, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h1107, h1765, h2248, h2252, hc23, hlam, hphi, p2261_1, u3elo3]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [h2257, hlam, p2261_0]
                                    · have p2261_0 := h2261c.1
                                      have p2261_1 := h2261c.2.1
                                      have p2261_2 := h2261c.2.2.1
                                      have p2261_3 := h2261c.2.2.2
                                      linarith only [hlam, p2261_0]
                                  · linarith only [h2259, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1766, h2259, hlam, ht01, ht12, ht23, u3elo3]
                                  · linarith only [h1107, h2248, h2252, h2259, hlam, ht01, ht12, ht23, u3elo3]
                                · linarith only [h1766, h2244, h2258, hlam]
                              · linarith only [h1766, h2244, h2253, h2257, hc23, hlam, hphi, u3elo3]
                        · linarith only [h1766, h2244, h2245, h2248, h2252, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1765, h2247, hlam]
                · linarith only [h0, h1764, h2246, hlam]
              · linarith only [h0, h1765, h2245, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2316 | h2316
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2317 | h2317
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2318 | h2318
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2319 | h2319
                    · linarith only [h1766, h2319, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2321 | h2321
                      · linarith only [h2319, h2321, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2323 | h2323
                        · linarith only [h1763, h1766, h2244, h2319, h2323, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2325 | h2325
                          · linarith only [h1763, h2319, h2325, hc13, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2327 | h2327
                            · linarith only [h1107, h2316, h2321, h2327, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2329 | h2329
                              · linarith only [h1764, h2244, h2329, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2331 | h2331
                                · linarith only [h1766, h2244, h2331, hc03, hlam, hphi, u3elo3]
                                · rcases h0emin with h2333 | h2333 | h2333 | h2333 | h2333
                                  · linarith only [h1107, h2321, h2333, hlam, ht01, ht12, ht23, u3elo4]
                                  · rcases h2bigk with h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h0, hlam, p2335_1]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      rcases p2335_3 (m.d 0 2) (by simp) with h2338 | h2338
                                      · rcases p2335_3 (m.d 1 2) (by simp) with h2339 | h2339
                                        · rcases p2335_3 (m.d 2 3) (by simp) with h2340 | h2340
                                          · linarith only [h2340, hlam, p2335_0]
                                          · rcases p2335_3 (m.d 2 4) (by simp) with h2342 | h2342
                                            · linarith only [h1764, h2342, hlam]
                                            · linarith only [h2325, h2342, hlam]
                                        · linarith only [h2316, h2339, hlam]
                                      · linarith only [h2338, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      rcases p2335_3 (m.d 0 2) (by simp) with h2347 | h2347
                                      · rcases p2335_3 (m.d 1 2) (by simp) with h2348 | h2348
                                        · rcases p2335_3 (m.d 2 3) (by simp) with h2349 | h2349
                                          · linarith only [h1763, h2349, hlam]
                                          · rcases p2335_3 (m.d 2 4) (by simp) with h2351 | h2351
                                            · linarith only [h2351, hlam, p2335_0]
                                            · rcases p2335_3 (m.d 2 5) (by simp) with h2353 | h2353
                                              · linarith only [h1765, h2353, hlam]
                                              · linarith only [h2329, h2353, hlam]
                                        · linarith only [h2317, h2348, hlam]
                                      · linarith only [h2347, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      rcases p2335_3 (m.d 0 2) (by simp) with h2358 | h2358
                                      · rcases p2335_3 (m.d 1 2) (by simp) with h2359 | h2359
                                        · rcases p2335_3 (m.d 2 3) (by simp) with h2360 | h2360
                                          · linarith only [h1763, h2360, hlam]
                                          · rcases p2335_3 (m.d 2 4) (by simp) with h2362 | h2362
                                            · linarith only [h1764, h2362, hlam]
                                            · rcases p2335_3 (m.d 2 5) (by simp) with h2364 | h2364
                                              · linarith only [h2364, hlam, p2335_0]
                                              · rcases h2emin with h2366 | h2366 | h2366 | h2366 | h2366
                                                · rcases h5bigk with h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c | h2367c
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [hlam, p2367_0]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h1107, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h1107, h2321, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2367_1, u3elo4, u5ehi2]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2242, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2244, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2321, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2367_1, u3elo4, u5ehi0]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [hlam, p2367_0]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2321, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2367_1, u3elo4, u5ehi2]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2321, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2323, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h1765, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2318, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [hlam, p2367_0]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2327, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2329, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h1765, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2367_1, u3elo4, u5ehi2]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2367_1, u3elo4, u5ehi1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2367_1, u3elo4, u5ehi2]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [hlam, p2367_0]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h2331, hlam, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    rcases p2367_3 (m.d 0 5) (by simp) with h2388 | h2388
                                                    · linarith only [h2244, h2388, hlam]
                                                    · rcases p2367_3 (m.d 1 5) (by simp) with h2390 | h2390
                                                      · linarith only [h2323, h2390, hlam]
                                                      · linarith only [h1107, h2390, hlam]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h1107, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    rcases p2367_3 (m.d 0 5) (by simp) with h2394 | h2394
                                                    · linarith only [h2244, h2394, hlam]
                                                    · linarith only [h1765, h2394, hlam]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [h1763, h2242, hc23, hc45, hlam, hphi, ht34, p2367_1]
                                                  · have p2367_0 := h2367c.1
                                                    have p2367_1 := h2367c.2.1
                                                    have p2367_2 := h2367c.2.2.1
                                                    have p2367_3 := h2367c.2.2.2
                                                    linarith only [hlam, p2367_0]
                                                · rcases h5bigk with h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c | h2399c
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [hlam, p2399_0]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h1107, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2242, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2399_1, u3elo4, u5ehi2]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2242, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2244, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2321, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2399_1, u3elo4, u5ehi0]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [hlam, p2399_0]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2321, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2399_1, u3elo4, u5ehi2]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2321, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2323, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h1765, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2318, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [hlam, p2399_0]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2327, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2329, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h1765, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2399_1, u3elo4, u5ehi2]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2399_1, u3elo4, u5ehi1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2399_1, u3elo4, u5ehi2]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [hlam, p2399_0]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h2331, hlam, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    rcases p2399_3 (m.d 0 5) (by simp) with h2420 | h2420
                                                    · linarith only [h2244, h2420, hlam]
                                                    · rcases p2399_3 (m.d 1 5) (by simp) with h2422 | h2422
                                                      · linarith only [h2323, h2422, hlam]
                                                      · linarith only [h1107, h2422, hlam]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h1107, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    rcases p2399_3 (m.d 0 5) (by simp) with h2426 | h2426
                                                    · linarith only [h2244, h2426, hlam]
                                                    · linarith only [h1765, h2426, hlam]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [h1763, h2242, hc23, hc45, hlam, hphi, ht34, p2399_1]
                                                  · have p2399_0 := h2399c.1
                                                    have p2399_1 := h2399c.2.1
                                                    have p2399_2 := h2399c.2.2.1
                                                    have p2399_3 := h2399c.2.2.2
                                                    linarith only [hlam, p2399_0]
                                                · linarith only [h1763, h2366, hlam, ht23, u3elo0]
                                                · linarith only [h1764, h1766, h2331, h2366, hc45, hlam, ht23, ht34]
                                                · linarith only [h0, h2366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2335_1]
                                        · linarith only [h2318, h2359, hlam]
                                      · linarith only [h2358, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h2333, hc12, hlam, ht01, p2335_1]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      rcases p2335_3 (m.d 0 2) (by simp) with h2438 | h2438
                                      · linarith only [h0, h2438, hlam]
                                      · linarith only [h1763, h2438, hlam]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      rcases p2335_3 (m.d 0 2) (by simp) with h2441 | h2441
                                      · linarith only [h0, h2441, hlam]
                                      · linarith only [h1764, h2441, hlam]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      rcases p2335_3 (m.d 0 2) (by simp) with h2444 | h2444
                                      · linarith only [h0, h2444, hlam]
                                      · linarith only [h1765, h2444, hlam]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h1763, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h2316, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h2325, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h2327, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h1764, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h2317, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h1107, h1764, h2244, h2321, hc23, hlam, hphi, p2335_1, u3elo4]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h2329, hlam, p2335_1]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h1765, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h2318, hlam, p2335_0]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h1107, h1765, h2321, hc23, hlam, hphi, p2335_1, u3elo4]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [h1107, h1765, h2321, h2325, hc23, hlam, hphi, p2335_1, u3elo4]
                                    · have p2335_0 := h2335c.1
                                      have p2335_1 := h2335c.2.1
                                      have p2335_2 := h2335c.2.2.1
                                      have p2335_3 := h2335c.2.2.2
                                      linarith only [hlam, p2335_0]
                                  · linarith only [h1766, h2331, h2333, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h1766, h2331, h2333, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h1107, h2321, h2333, hlam, ht01, ht12, ht23, u3elo4]
                  · linarith only [h0, h1765, h2318, hlam]
                · linarith only [h0, h1764, h2317, hlam]
              · linarith only [h0, h1765, h2316, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2468 | h2468
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2469 | h2469
          · linarith only [h1763, h1765, h2469, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2471 | h2471
            · linarith only [h2468, h2469, h2471, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2473 | h2473
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2474 | h2474
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2475 | h2475
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2476 | h2476
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2477 | h2477
                      · linarith only [h2469, h2477, hc03, hlam, hphi, u3elo1]
                      · linarith only [h1763, h1765, h2475, h2477, hc23, hlam, hphi, u3elo4]
                    · linarith only [h2468, h2476, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2481 | h2481
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2482 | h2482
                      · linarith only [h2469, h2482, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2484 | h2484
                        · linarith only [h1763, h1765, h2471, h2474, h2475, h2482, h2484, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2486 | h2486
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2487 | h2487
                            · linarith only [h1763, h2482, h2487, hc13, hlam, hphi, u3elo0]
                            · linarith only [h1763, h1765, h2486, h2487, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h2468, h2469, h2486, hc23, hlam, hphi, u3elo4]
                    · linarith only [h2468, h2469, h2473, h2481, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h1764, h2474, hlam]
              · linarith only [h0, h2473, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2494 | h2494
          · linarith only [h2468, h2494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2496 | h2496
            · linarith only [h1764, h1765, h2496, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2498 | h2498
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2499 | h2499
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2500 | h2500
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2501 | h2501
                    · linarith only [h2468, h2501, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2503 | h2503
                      · linarith only [h1765, h2494, h2501, h2503, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1763, h1765, h2500, h2503, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2506 | h2506
                    · linarith only [h1763, h2468, h2506, hc23, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2508 | h2508
                      · linarith only [h2506, h2508, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2510 | h2510
                        · linarith only [h1763, h2468, h2496, h2499, h2500, h2508, h2510, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2512 | h2512
                          · linarith only [h1763, h2506, h2512, hc13, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2514 | h2514
                            · linarith only [h0, h1764, h2500, h2508, h2512, h2514, hlam]
                            · linarith only [h1764, h1765, h2512, h2514, hc23, hlam, hphi, u3elo4]
                · linarith only [h1764, h1765, h2499, hc12, hc25, hlam, hphi]
              · linarith only [h0, h1763, h2498, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2519 | h2519
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2520 | h2520
        · linarith only [h1763, h1764, h2520, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2522 | h2522
          · linarith only [h2520, h2522, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2524 | h2524
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2525 | h2525
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2526 | h2526
                · linarith only [h1764, h2519, h2526, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2528 | h2528
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2529 | h2529
                    · linarith only [h2520, h2529, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2531 | h2531
                      · linarith only [h2522, h2529, h2531, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2533 | h2533
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2534 | h2534
                          · linarith only [h1763, h2529, h2534, hc13, hlam, hphi, u3elo0]
                          · linarith only [h1764, h2519, h2534, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                        · linarith only [h1107, h2524, h2526, h2528, h2533, hlam]
                  · linarith only [h0, h2519, h2528, hlam]
              · linarith only [h0, h1763, h2525, hlam]
            · linarith only [h1764, h2519, h2524, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2541 | h2541
        · linarith only [h1763, h1764, h2541, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2543 | h2543
          · linarith only [h2541, h2543, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2545 | h2545
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2546 | h2546
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2547 | h2547
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2548 | h2548
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2549 | h2549
                    · linarith only [h2541, h2549, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1763, h1764, h2547, h2549, hc23, hlam, hphi, u3elo3]
                  · linarith only [h1763, h1764, h2547, h2548, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2553 | h2553
                  · linarith only [h1763, h2519, h2547, h2553, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2555 | h2555
                    · linarith only [h1763, h2541, h2555, hc23, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2557 | h2557
                      · linarith only [h2543, h2555, h2557, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2559 | h2559
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2560 | h2560
                          · linarith only [h0, h1763, h2553, h2555, h2559, h2560, hc01, hlam, hphi, ht12, ht23, u3elo0]
                          · linarith only [h1763, h1764, h2560, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h1764, h2545, h2547, h2559, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h1763, h2546, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2565 | h2565
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2566 | h2566
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2567 | h2567
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2568 | h2568
                    · linarith only [h2541, h2568, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1763, h1764, h2566, h2568, hc23, hlam, hphi, u3elo3]
                  · linarith only [h1763, h1764, h2566, h2567, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2572 | h2572
                  · linarith only [h1763, h2519, h2566, h2572, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2574 | h2574
                    · linarith only [h1763, h2541, h2574, hc23, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2576 | h2576
                      · linarith only [h2543, h2574, h2576, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2578 | h2578
                        · linarith only [h1763, h1764, h2545, h2574, h2578, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2580 | h2580
                          · linarith only [h1763, h2574, h2580, hc13, hlam, hphi, u3elo0]
                          · linarith only [h1763, h1764, h2580, hc23, hlam, hphi, u3elo3]
              · linarith only [h1763, h1764, h2565, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2584 | h2584
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2585 | h2585
      · linarith only [h1763, h2585, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2587 | h2587
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2588 | h2588
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2589 | h2589
            · linarith only [h1763, h2584, h2589, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2591 | h2591
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2592 | h2592
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2593 | h2593
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2594 | h2594
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2595 | h2595
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2596 | h2596
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2597 | h2597
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2598 | h2598
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2599 | h2599
                              · linarith only [h2584, h2585, h2589, h2599, hlam]
                              · linarith only [h2584, h2585, h2594, h2596, h2597, h2599, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h1763, h2584, h2597, h2598, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h1763, h2584, h2597, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2604 | h2604
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2605 | h2605
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2606 | h2606
                              · linarith only [h2584, h2585, h2593, h2596, h2606, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2608 | h2608
                                · linarith only [h2584, h2585, h2593, h2596, h2604, h2608, hlam]
                                · rcases h0emin with h2610 | h2610 | h2610 | h2610 | h2610
                                  · linarith only [h0, h2610, hc12, hlam, ht01]
                                  · linarith only [h2585, h2593, h2610, hc15, hlam, ht01]
                                  · linarith only [h2610, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h2584, h2585, h2605, h2610, hc23, hlam, ht01, ht12]
                                  · linarith only [h2585, h2605, h2610, hlam, ht01, ht12, ht23, u3elo2]
                            · linarith only [h1763, h2588, h2605, hlam]
                          · linarith only [h1763, h2588, h2604, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · linarith only [h1763, h2588, h2591, h2595, hlam]
                    · linarith only [h1763, h2584, h2585, h2587, h2588, h2591, h2593, h2594, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h1763, h2584, h2591, h2593, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h1763, h2584, h2591, h2592, hlam]
              · linarith only [h0, h2591, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2623 | h2623
            · linarith only [h1763, h2584, h2623, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2625 | h2625
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2626 | h2626
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2627 | h2627
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2628 | h2628
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2629 | h2629
                      · linarith only [h1763, h2588, h2629, hc02, hlam, hphi, ht23, u3elo1]
                      · linarith only [h1763, h2584, h2625, h2629, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1763, h2584, h2625, h2628, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h1763, h2584, h2625, h2627, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h1763, h2584, h2625, h2626, hlam]
              · linarith only [h0, h2625, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h1763, h2584, h2587, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2637 | h2637
      · linarith only [h1763, h2637, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2639 | h2639
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2640 | h2640
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2641 | h2641
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2642 | h2642
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2643 | h2643
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2644 | h2644
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2645 | h2645
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2646 | h2646
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2647 | h2647
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2648 | h2648
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2649 | h2649
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2650 | h2650
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2651 | h2651
                                · linarith only [h2639, h2651, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                                · rcases h0emin with h2653 | h2653 | h2653 | h2653 | h2653
                                  · linarith only [h0, h2653, hc12, hlam, ht01]
                                  · linarith only [h2637, h2644, h2645, h2647, h2653, hlam, ht01, ht12, ht23, u3elo1]
                                  · linarith only [h1763, h2642, h2653, hlam, ht01, ht12, ht23, u3elo1]
                                  · linarith only [h2584, h2643, h2645, h2653, hlam, ht01, ht12, ht23, u3elo1]
                                  · linarith only [h1107, h2645, h2647, h2653, hlam, ht01, ht12, ht23, u3elo1]
                              · linarith only [h2584, h2641, h2650, hlam]
                            · linarith only [h0, h1763, h2649, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1763, h2639, h2641, h2648, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi4]
                        · linarith only [h0, h1763, h2584, h2639, h2641, h2643, h2647, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h1763, h2640, h2642, h2646, hlam]
                    · linarith only [h1763, h2639, h2642, h2645, hlam]
                  · linarith only [h1763, h2640, h2642, h2644, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h1763, h2639, h2641, h2642, h2643, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · linarith only [h0, h2642, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2668 | h2668
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2669 | h2669
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2670 | h2670
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2671 | h2671
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2672 | h2672
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2673 | h2673
                        · linarith only [h0, h2584, h2641, h2671, h2673, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2675 | h2675
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2676 | h2676
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2677 | h2677
                              · linarith only [h2669, h2673, h2677, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2679 | h2679
                                · linarith only [h0, h2584, h2669, h2673, h2679, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                · rcases h0emin with h2681 | h2681 | h2681 | h2681 | h2681
                                  · linarith only [h0, h2584, h2669, h2681, hc14, hlam, ht01]
                                  · linarith only [h2584, h2669, h2681, hc14, hlam, ht01]
                                  · linarith only [h1763, h2668, h2681, hlam, ht01, ht12, ht23, u3elo1]
                                  · linarith only [h1107, h2641, h2672, h2681, hlam, ht01, ht12, ht23, u3elo1]
                                  · linarith only [h1107, h2672, h2681, hlam, ht01, ht12, ht23, u3elo1]
                            · linarith only [h0, h1763, h2676, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1763, h2639, h2675, hlam]
                      · linarith only [h2640, h2672, hc13, hlam, hphi, u3elo0]
                    · linarith only [h1763, h2639, h2668, h2671, hlam]
                  · linarith only [h1763, h2640, h2668, h2670, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h1763, h2640, h2668, h2669, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h0, h2668, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2694 | h2694
            · linarith only [h2639, h2640, h2694, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2696 | h2696
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2697 | h2697
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2698 | h2698
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2699 | h2699
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2700 | h2700
                      · linarith only [h2640, h2700, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h1763, h2696, h2700, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h1763, h2696, h2699, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1763, h2696, h2698, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h1763, h2696, h2697, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h2696, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2707 | h2707
          · linarith only [h2639, h2707, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2709 | h2709
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2710 | h2710
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2711 | h2711
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2712 | h2712
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2713 | h2713
                    · linarith only [h2639, h2713, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h1763, h2710, h2713, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2584, h2711, h2712, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h1763, h2710, h2711, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h2710, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2719 | h2719
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2720 | h2720
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2721 | h2721
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2722 | h2722
                    · linarith only [h2639, h2722, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h1763, h2719, h2722, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1763, h2719, h2721, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h1763, h2719, h2720, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h2719, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 5456000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1107 | h1107
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x1_x0 m hb0 hb2 hb3 hb5 h0 h1107
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x1_x1 m hb0 hb2 hb3 hb5 h0 h1107

end R2N4
