import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1475 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1633 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1778 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1779 | h1779
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1780 | h1780
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1781 | h1781
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1782 | h1782
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1783 | h1783
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1784 | h1784
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1785 | h1785
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1786 | h1786
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1787 | h1787
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1788 | h1788
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1789 | h1789
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1790 | h1790
                        · rcases h4bigk with h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1475, hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1780, h1787, h1790, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi4]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1314, h1780, h1782, h1790, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi4]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            rcases p1791_3 (m.d 0 4) (by simp) with h1796 | h1796
                            · rcases p1791_3 (m.d 1 4) (by simp) with h1797 | h1797
                              · rcases p1791_3 (m.d 2 4) (by simp) with h1798 | h1798
                                · linarith only [h1779, h1798, hlam]
                                · linarith only [h1789, h1798, hlam]
                              · linarith only [h1786, h1797, hlam]
                            · linarith only [h1796, hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1475, h1782, h1784, hc01, hc12, hlam, hphi, p1791_1]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1782, h1784, h1787, h1790, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi4]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1782, h1784, h1790, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi4]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            rcases p1791_3 (m.d 0 4) (by simp) with h1807 | h1807
                            · linarith only [h1475, h1807, hlam]
                            · linarith only [h1781, h1807, hlam]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1779, hlam, p1791_1]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1783, hlam, p1791_1]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1779, h1790, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi4]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h0, h1778, h1787, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1791_1]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1780, hlam, p1791_1]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1784, hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1787, hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1314, h1780, h1782, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1791_1]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1781, hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1786, hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1789, hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [h1790, hlam, p1791_0]
                          · have p1791_0 := h1791c.1
                            have p1791_1 := h1791c.2.1
                            have p1791_2 := h1791c.2.2.1
                            have p1791_3 := h1791c.2.2.2
                            linarith only [hlam, p1791_0]
                        · linarith only [h0, h1778, h1787, h1789, h1790, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1826 | h1826
                        · linarith only [h1787, h1789, h1826, hlam]
                        · rcases h4bigk with h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1475, hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1475, h1782, h1784, h1787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1828_1, u3ehi3]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1475, h1782, h1784, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1828_1, u3ehi3]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1475, h1782, h1784, h1787, h1789, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1828_1, u3ehi3]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1475, h1782, h1784, hc01, hc12, hlam, hphi, p1828_1]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1782, h1784, h1787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1828_1, u3ehi3]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1782, h1784, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1828_1, u3ehi3]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1782, h1784, h1787, h1789, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1828_1, u3ehi3]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1779, hlam, p1828_1]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1783, hlam, p1828_1]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1781, h1789, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1828_1, u3ehi3]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1789, hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1780, hlam, p1828_1]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1784, hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1787, hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1826, hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1781, hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1786, hlam, p1828_0]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1781, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p1828_1]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [h1475, h1781, h1782, h1784, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1828_1, u3ehi3]
                          · have p1828_0 := h1828c.1
                            have p1828_1 := h1828c.2.1
                            have p1828_2 := h1828c.2.2.1
                            have p1828_3 := h1828c.2.2.2
                            linarith only [hlam, p1828_0]
                    · linarith only [h1782, h1785, h1787, h1788, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1855 | h1855
                    · linarith only [h1787, h1855, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1857 | h1857
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1858 | h1858
                        · rcases h4bigk with h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1475, hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1475, h1782, h1784, h1857, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1475, h1782, h1784, h1855, h1858, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1859_1, u3ehi2]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            rcases p1859_3 (m.d 0 4) (by simp) with h1864 | h1864
                            · rcases p1859_3 (m.d 1 4) (by simp) with h1865 | h1865
                              · rcases p1859_3 (m.d 2 4) (by simp) with h1866 | h1866
                                · linarith only [h1779, h1866, hlam]
                                · linarith only [h1857, h1866, hlam]
                              · linarith only [h1786, h1865, hlam]
                            · linarith only [h1864, hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1475, h1782, h1784, hc01, hc12, hlam, hphi, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1782, h1784, h1855, h1857, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1859_1, u3ehi2]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1782, h1784, h1855, h1858, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1859_1, u3ehi2]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            rcases p1859_3 (m.d 0 4) (by simp) with h1875 | h1875
                            · linarith only [h1475, h1875, hlam]
                            · linarith only [h1781, h1875, hlam]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1779, hlam, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1783, hlam, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1787, hlam, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h0, h1779, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1780, hlam, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1784, hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1314, h1780, h1782, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1314, h1780, h1782, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1859_1]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1781, hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1786, hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1857, hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [h1858, hlam, p1859_0]
                          · have p1859_0 := h1859c.1
                            have p1859_1 := h1859c.2.1
                            have p1859_2 := h1859c.2.2.1
                            have p1859_3 := h1859c.2.2.2
                            linarith only [hlam, p1859_0]
                        · linarith only [h1475, h1781, h1782, h1784, h1787, h1858, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1894 | h1894
                        · linarith only [h1314, h1780, h1782, h1787, h1857, h1894, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1787, h1894, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h1475, h1781, h1786, hlam]
              · linarith only [h1314, h1780, h1785, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1314, h1780, h1784, hlam]
          · linarith only [h0, h1779, h1783, hlam]
        · linarith only [h0, h1778, h1782, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1902 | h1902
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1903 | h1903
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1904 | h1904
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1905 | h1905
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1906 | h1906
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1907 | h1907
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1908 | h1908
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1909 | h1909
                      · linarith only [h1779, h1781, h1909, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1911 | h1911
                        · linarith only [h1779, h1781, h1907, h1911, hlam]
                        · rcases h4bigk with h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1475, hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1907, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1913_1, u3ehi3]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1781, h1902, h1904, h1906, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1913_1, u3ehi3]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1781, hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1475, h1902, h1904, hc01, hc12, hlam, hphi, p1913_1]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1902, h1904, h1907, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1913_1, u3ehi3]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1902, h1904, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1913_1, u3ehi3]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1633, h1781, h1902, h1904, hc01, hc12, hlam, hphi, p1913_1]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1779, hlam, p1913_1]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1903, hlam, p1913_1]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1779, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1913_1, u3ehi3]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1909, hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1780, hlam, p1913_1]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1904, hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1907, hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1911, hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p1913_1]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1906, hlam, p1913_0]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1902, h1904, h1906, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1913_1]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [h1902, h1904, h1906, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1913_1, u3ehi3]
                          · have p1913_0 := h1913c.1
                            have p1913_1 := h1913c.2.1
                            have p1913_2 := h1913c.2.2.1
                            have p1913_3 := h1913c.2.2.2
                            linarith only [hlam, p1913_0]
                    · linarith only [h1902, h1905, h1907, h1908, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1780, h1781, h1902, h1904, h1906, h1907, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1941 | h1941
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1942 | h1942
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1943 | h1943
                      · linarith only [h1475, h1906, h1943, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1945 | h1945
                        · linarith only [h1475, h1778, h1906, h1941, h1945, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h4bigk with h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1475, hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1941, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1947_1, u3ehi3]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1947_1, u3ehi3]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1781, hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1906, hc04, hc45, hlam, hphi, p1947_1]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1906, h1941, hc45, hlam, hphi, ht34, p1947_1, u3ehi3]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1906, hc45, hlam, hphi, ht34, p1947_1, u3ehi3]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1906, hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1779, hlam, p1947_1]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1903, hlam, p1947_1]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1779, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1947_1, u3ehi3]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1943, hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1780, hlam, p1947_1]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1904, hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1941, hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1945, hlam, p1947_0]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p1947_1]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hc14, hc45, hlam, hphi, p1947_1]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [h1941, hc45, hlam, hphi, ht34, p1947_1, u3ehi3]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1947_1, u3ehi3]
                          · have p1947_0 := h1947c.1
                            have p1947_1 := h1947c.2.1
                            have p1947_2 := h1947c.2.2.1
                            have p1947_3 := h1947c.2.2.2
                            linarith only [hlam, p1947_0]
                    · linarith only [h1902, h1905, h1941, h1942, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1780, h1781, h1941, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1314, h1780, h1905, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1314, h1780, h1904, hlam]
          · linarith only [h0, h1779, h1903, hlam]
        · linarith only [h0, h1778, h1902, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1979 | h1979
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1980 | h1980
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1981 | h1981
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1982 | h1982
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1983 | h1983
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1984 | h1984
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1985 | h1985
                  · linarith only [h1778, h1780, h1985, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1987 | h1987
                    · linarith only [h1778, h1780, h1982, h1987, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1989 | h1989
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1990 | h1990
                        · rcases h4bigk with h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1475, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1987, h1989, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1991_1, u3ehi2]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1780, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1780, h1980, h1982, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1475, hc01, hc14, hlam, hphi, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1981, h1987, h1989, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1991_1, u3ehi2]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1980, h1982, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1991_1, u3ehi3]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            rcases p1991_3 (m.d 0 4) (by simp) with h2001 | h2001
                            · linarith only [h1475, h2001, hlam]
                            · linarith only [h1979, h2001, hlam]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1779, hlam, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1981, hlam, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1985, hlam, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h0, h1779, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1475, hc01, hc34, hlam, hphi, ht12, ht23, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1982, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1980, h1982, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1980, h1982, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1979, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1984, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1989, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1990, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                        · linarith only [h1778, h1780, h1990, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h1780, h1979, h1980, h1982, h1985, h1989, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h1475, h1780, h1979, h1980, h1982, h1984, hc01, hc12, hlam, hphi]
              · linarith only [h1780, h1982, h1983, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2023 | h2023
              · linarith only [h1982, h2023, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2025 | h2025
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2026 | h2026
                  · linarith only [h1314, h1982, h2026, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2028 | h2028
                    · linarith only [h1314, h1778, h2023, h2028, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2030 | h2030
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2031 | h2031
                        · rcases h4bigk with h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1475, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1475, h2028, h2030, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2032_1, u3ehi2]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1780, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            rcases p2032_3 (m.d 0 4) (by simp) with h2037 | h2037
                            · rcases p2032_3 (m.d 1 4) (by simp) with h2038 | h2038
                              · rcases p2032_3 (m.d 2 4) (by simp) with h2039 | h2039
                                · linarith only [h1779, h2039, hlam]
                                · linarith only [h2030, h2039, hlam]
                              · linarith only [h2025, h2038, hlam]
                            · linarith only [h2037, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1475, h1982, hc01, hc34, hlam, hphi, ht12, ht23, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1982, h2028, h2030, hc34, hlam, hphi, p2032_1, u3ehi2]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1982, hlam, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            rcases p2032_3 (m.d 0 4) (by simp) with h2048 | h2048
                            · linarith only [h1475, h2048, hlam]
                            · linarith only [h1979, h2048, hlam]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1779, hlam, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1981, hlam, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h2026, hlam, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h0, h1779, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1475, hc01, hc34, hlam, hphi, ht12, ht23, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1475, hc01, hc34, hlam, hphi, ht12, ht23, p2032_1]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h2026, hc34, hlam, hphi, p2032_1, u3ehi2]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            rcases p2032_3 (m.d 0 4) (by simp) with h2060 | h2060
                            · linarith only [h1780, h2060, hlam]
                            · linarith only [h1979, h2060, hlam]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h1979, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h2025, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h2030, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [h2031, hlam, p2032_0]
                          · have p2032_0 := h2032c.1
                            have p2032_1 := h2032c.2.1
                            have p2032_2 := h2032c.2.2.1
                            have p2032_3 := h2032c.2.2.2
                            linarith only [hlam, p2032_0]
                        · linarith only [h1778, h1780, h2031, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h1475, h1979, h1982, h2026, h2030, hc34, hlam, hphi, u3ehi2]
                · linarith only [h1475, h1979, h2025, hlam]
          · linarith only [h0, h1779, h1981, hlam]
        · linarith only [h0, h1778, h1780, h1980, hc01, hc34, hlam, hphi, ht12, ht23]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2073 | h2073
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2074 | h2074
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2075 | h2075
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2076 | h2076
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2077 | h2077
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2078 | h2078
                  · linarith only [h1778, h1780, h2078, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2080 | h2080
                    · linarith only [h1778, h1780, h1979, h2073, h2075, h2077, h2080, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2082 | h2082
                      · linarith only [h1779, h1780, h1979, h2082, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2084 | h2084
                        · linarith only [h1778, h1780, h1979, h2084, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1778, h1780, h2073, h2075, h2077, h2084, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h1778, h1780, h2075, h2077, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1778, h1780, h2075, h2076, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2089 | h2089
              · linarith only [h2075, h2089, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2091 | h2091
                · linarith only [h1778, h1780, h1979, h2075, h2091, hc34, hlam, hphi, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2093 | h2093
                  · linarith only [h1314, h1778, h2089, h2093, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2095 | h2095
                    · linarith only [h1314, h1778, h2075, h2091, h2095, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2097 | h2097
                      · linarith only [h1314, h2075, h2091, h2097, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2099 | h2099
                        · linarith only [h1475, h2091, h2099, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1778, h1780, h2099, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h1779, h2074, hlam]
        · linarith only [h0, h1778, h2073, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2104 | h2104
    · linarith only [h1778, h1779, h2104, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2106 | h2106
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2107 | h2107
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2108 | h2108
          · linarith only [h1778, h1779, h2108, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2110 | h2110
            · linarith only [h2104, h2107, h2108, h2110, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2112 | h2112
              · linarith only [h2110, h2112, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2114 | h2114
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2115 | h2115
                  · linarith only [h1314, h1778, h2110, h2115, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1778, h2108, h2115, hc34, hlam, hphi, u3ehi2]
                · linarith only [h1475, h2106, h2114, hlam]
        · linarith only [h0, h1778, h2107, hlam]
      · linarith only [h1778, h1779, h2106, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
