import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5150000 in
set_option maxHeartbeats 5150000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1334 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1526 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1712 | h1712
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1713 | h1713
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1714 | h1714
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1715 | h1715
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1716 | h1716
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1717 | h1717
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1718 | h1718
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1719 | h1719
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1720 | h1720
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1721 | h1721
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1722 | h1722
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1723 | h1723
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1724 | h1724
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1726 | h1726
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1727 | h1727
                                · linarith only [h1713, h1724, h1727, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h0, h1713, h1724, h1726, h1727, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1730 | h1730
                                · linarith only [h1724, h1726, h1730, hlam]
                                · rcases h0bigk with h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h0, hlam, p1732_1]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1334, hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1526, hlam, p1732_1]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1526, h1719, h1722, hc12, hlam, hphi, ht01, ht0b, ht5b, p1732_1, u5ehi0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1732_1]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h0, h1716, h1718, h1724, h1726, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1732_1, u3ehi3]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h0, h1718, h1724, h1726, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1732_1, u3ehi3]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h0, h1712, h1721, h1725, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1732_1, u3ehi4]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1712, h1721, h1725, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1732_1, u3ehi4]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1713, hlam, p1732_1]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1334, h1718, h1719, h1724, h1726, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1732_1, u3ehi3]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1334, h1712, h1719, h1721, h1725, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1732_1, u3ehi4]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1712, h1721, h1725, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1732_1, u3ehi4]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1714, hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1716, hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1526, h1712, h1719, h1721, h1722, h1725, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1732_1, u3ehi4]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1712, hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1715, hlam, p1732_1]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1717, hlam, p1732_0]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [h1718, hlam, p1732_1]
                                  · have p1732_0 := h1732c.1
                                    have p1732_1 := h1732c.2.1
                                    have p1732_2 := h1732c.2.2.1
                                    have p1732_3 := h1732c.2.2.2
                                    linarith only [hlam, p1732_0]
                            · linarith only [h1526, h1712, h1719, h1722, h1723, h1725, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1759 | h1759
                            · linarith only [h1724, h1759, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1526, h1712, h1719, h1722, h1723, h1759, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1526, h1712, h1722, h1723, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h1334, h1716, h1722, hlam]
                    · linarith only [h0, h1712, h1721, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h1712, h1720, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1712, h1719, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h1526, h1712, h1718, hlam]
            · linarith only [h1716, h1717, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1769 | h1769
            · linarith only [h1716, h1769, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1334, h1712, h1769, hlam]
        · linarith only [h0, h1712, h1715, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1773 | h1773
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1774 | h1774
          · linarith only [h1713, h1714, h1774, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1776 | h1776
            · linarith only [h1774, h1776, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1334, h1712, h1776, hlam]
        · linarith only [h1334, h1712, h1713, h1773, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1780 | h1780
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1781 | h1781
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1782 | h1782
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1783 | h1783
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1784 | h1784
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1785 | h1785
                · linarith only [h1713, h1781, h1785, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h1712, h1785, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h1526, h1712, h1784, hlam]
            · linarith only [h1782, h1783, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1713, h1780, h1782, hlam]
        · linarith only [h1526, h1712, h1780, h1781, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1792 | h1792
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1793 | h1793
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1794 | h1794
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1795 | h1795
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1796 | h1796
                · linarith only [h1713, h1792, h1796, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h1712, h1796, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1712, h1780, h1795, hlam]
            · linarith only [h1793, h1794, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1801 | h1801
            · linarith only [h1793, h1801, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1334, h1712, h1801, hlam]
        · linarith only [h0, h1712, h1792, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1805 | h1805
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1806 | h1806
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1807 | h1807
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1808 | h1808
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1809 | h1809
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1810 | h1810
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1811 | h1811
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1812 | h1812
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1813 | h1813
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1814 | h1814
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1815 | h1815
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1816 | h1816
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1817 | h1817
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1818 | h1818
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1819 | h1819
                                · linarith only [h1805, h1816, h1819, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h1805, h1816, h1818, h1819, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1822 | h1822
                                · linarith only [h1816, h1818, h1822, hlam]
                                · rcases h0bigk with h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [hlam, p1824_0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h0, hlam, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1334, hlam, p1824_0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1526, hlam, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1712, hlam, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [hlam, p1824_0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h0, h1808, h1810, h1816, h1818, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1824_1, u3ehi3]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h0, h1810, h1816, h1818, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1824_1, u3ehi3]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1824_1, u5ehi0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1334, h1811, hc01, hc12, hlam, hphi, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1805, hlam, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [hlam, p1824_0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1334, h1810, h1811, h1816, h1818, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1824_1, u3ehi3]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1334, h1807, h1811, hc12, hlam, hphi, ht01, ht0b, ht5b, p1824_1, u5ehi2]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1526, h1811, h1814, hc01, hc12, hlam, hphi, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1806, hlam, p1824_0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1808, hlam, p1824_0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [hlam, p1824_0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1526, h1811, h1814, hc12, hlam, hphi, ht01, ht0b, ht5b, p1824_1, u5ehi0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1712, hc01, hc15, hlam, hphi, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1807, hlam, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1809, hlam, p1824_0]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [h1810, hlam, p1824_1]
                                  · have p1824_0 := h1824c.1
                                    have p1824_1 := h1824c.2.1
                                    have p1824_2 := h1824c.2.2.1
                                    have p1824_3 := h1824c.2.2.2
                                    linarith only [hlam, p1824_0]
                            · linarith only [h1334, h1809, h1811, h1816, h1817, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1851 | h1851
                            · linarith only [h1816, h1851, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1853 | h1853
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1854 | h1854
                                · rcases h0bigk with h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h0, hlam, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1334, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1526, hlam, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1712, hlam, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1855_1, u3ehi0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h0, h1810, hc12, hlam, hphi, ht01, ht0b, ht5b, p1855_1, u5ehi0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1855_1, u5ehi0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1334, h1811, hc01, hc12, hlam, hphi, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1805, hlam, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1334, h1806, h1811, h1853, hc12, hlam, hphi, ht01, ht0b, ht5b, p1855_1, u5ehi4]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1334, h1807, h1811, h1851, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1855_1, u3ehi2]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1526, h1811, h1814, hc01, hc12, hlam, hphi, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1806, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1808, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1526, h1809, h1811, h1814, h1851, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1855_1, u3ehi2]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1712, h1811, h1815, hc01, hc12, hlam, hphi, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1807, hlam, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1809, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1810, hlam, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                · linarith only [h0, h1806, h1853, h1854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1882 | h1882
                                · linarith only [h1334, h1808, h1811, h1816, h1853, h1882, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h1526, h1810, h1811, h1814, h1816, h1882, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1334, h1808, h1815, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1334, h1808, h1814, hlam]
                    · linarith only [h0, h1807, h1813, hlam]
                  · linarith only [h0, h1806, h1812, hlam]
                · linarith only [h0, h1805, h1811, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1890 | h1890
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1891 | h1891
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1892 | h1892
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1893 | h1893
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1894 | h1894
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1895 | h1895
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1896 | h1896
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1897 | h1897
                              · linarith only [h1806, h1810, h1897, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1899 | h1899
                                · linarith only [h1805, h1810, h1895, h1899, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
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
                                    linarith only [h0, hlam, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1334, hlam, p1901_0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1526, hlam, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1712, hlam, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [hlam, p1901_0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1901_1, u3ehi0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h0, h1806, h1895, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1901_1, u3ehi3]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1901_1, u5ehi0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1334, hc01, hc13, hlam, hphi, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1805, hlam, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [hlam, p1901_0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h0, h1805, h1806, h1895, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1901_1, u3ehi3]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h0, h1805, h1807, h1896, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1901_1, u3ehi4]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1810, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1806, hlam, p1901_0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1808, hlam, p1901_0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [hlam, p1901_0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1810, hlam, p1901_0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1712, hc01, hc15, hlam, hphi, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1807, hlam, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1809, hlam, p1901_0]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [h1810, hc04, hc45, hlam, hphi, p1901_1]
                                  · have p1901_0 := h1901c.1
                                    have p1901_1 := h1901c.2.1
                                    have p1901_2 := h1901c.2.2.1
                                    have p1901_3 := h1901c.2.2.2
                                    linarith only [hlam, p1901_0]
                            · linarith only [h0, h1805, h1809, h1895, h1896, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1808, h1810, h1895, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h0, h1334, h1805, h1809, h1894, hc01, hc12, hlam, hphi]
                      · linarith only [h1334, h1808, h1810, h1893, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h0, h1807, h1892, hlam]
                  · linarith only [h0, h1806, h1891, hlam]
                · linarith only [h0, h1805, h1890, hlam]
            · linarith only [h1808, h1809, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1935 | h1935
            · linarith only [h1808, h1935, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1937 | h1937
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1939 | h1939
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1940 | h1940
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1941 | h1941
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1942 | h1942
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1943 | h1943
                          · linarith only [h1805, h1808, h1943, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1945 | h1945
                            · linarith only [h1805, h1935, h1945, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1947 | h1947
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1948 | h1948
                                · rcases h0bigk with h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [hlam, p1949_0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h0, hlam, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1334, hlam, p1949_0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1526, hlam, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1712, hlam, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [hlam, p1949_0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h0, h1937, hc12, hlam, hphi, ht01, ht0b, ht5b, p1949_1, u5ehi0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1949_1, u5ehi0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1334, h1938, hc01, hc12, hlam, hphi, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1805, hlam, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [hlam, p1949_0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1808, hlam, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1935, hlam, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1526, hc01, hc14, hlam, hphi, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1806, hlam, p1949_0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1808, h1938, h1941, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [hlam, p1949_0]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1805, h1808, h1935, h1938, h1941, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi2]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1712, h1938, h1942, hc01, hc12, hlam, hphi, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1807, hlam, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1805, h1935, h1938, h1941, h1948, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi2]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [h1937, hlam, p1949_1]
                                  · have p1949_0 := h1949c.1
                                    have p1949_1 := h1949c.2.1
                                    have p1949_2 := h1949c.2.2.1
                                    have p1949_3 := h1949c.2.2.2
                                    linarith only [hlam, p1949_0]
                                · linarith only [h0, h1806, h1947, h1948, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1808, h1937, h1943, h1947, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1808, h1937, h1941, h1942, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1978 | h1978
                        · linarith only [h1941, h1978, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1980 | h1980
                          · linarith only [h1334, h1941, h1980, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1982 | h1982
                            · linarith only [h1334, h1805, h1941, h1982, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1984 | h1984
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1985 | h1985
                                · rcases h0bigk with h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c | h1986c
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [hlam, p1986_0]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h0, hlam, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1334, hlam, p1986_0]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1526, hlam, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1712, hlam, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [hlam, p1986_0]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1986_1, u3ehi0]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h0, h1805, h1935, h1937, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1986_1, u3ehi2]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h0, h1805, h1935, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1986_1, u3ehi2]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1334, hc01, hc13, hlam, hphi, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1805, hlam, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [hlam, p1986_0]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1808, hlam, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1935, hlam, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1526, hc01, hc14, hlam, hphi, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1806, hlam, p1986_0]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1808, hc34, hlam, hphi, p1986_1, u3ehi0]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [hlam, p1986_0]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1805, h1808, h1935, hc34, hlam, hphi, p1986_1, u3ehi2]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1712, hc01, hc15, hlam, hphi, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1807, hlam, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1805, h1935, h1985, hc34, hlam, hphi, p1986_1, u3ehi2]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [h1937, hlam, p1986_1]
                                  · have p1986_0 := h1986c.1
                                    have p1986_1 := h1986c.2.1
                                    have p1986_2 := h1986c.2.2.1
                                    have p1986_3 := h1986c.2.2.2
                                    linarith only [hlam, p1986_0]
                                · linarith only [h1526, h1941, h1984, h1985, hc01, hc24, hlam, hphi, ht12]
                              · linarith only [h1808, h1937, h1980, h1984, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h1807, h1940, hlam]
                  · linarith only [h0, h1806, h1939, hlam]
                · linarith only [h0, h1805, h1938, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2017 | h2017
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2018 | h2018
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2019 | h2019
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2020 | h2020
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2021 | h2021
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2022 | h2022
                          · linarith only [h1805, h1808, h2022, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2024 | h2024
                            · linarith only [h1805, h1808, h1935, h2017, h2020, h2024, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2026 | h2026
                              · linarith only [h0, h1526, h1806, h1937, h2026, hc01, hc12, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2028 | h2028
                                · linarith only [h1805, h1808, h1937, h2020, h2028, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h1805, h1808, h2028, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h1805, h1808, h2020, h2021, hc35, hlam, hphi, u3ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2032 | h2032
                        · linarith only [h2020, h2032, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2034 | h2034
                          · linarith only [h1334, h2020, h2034, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2036 | h2036
                            · linarith only [h1334, h1805, h2020, h2036, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2038 | h2038
                              · linarith only [h1806, h1937, h2038, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2040 | h2040
                                · linarith only [h1808, h1937, h2040, hc34, hlam, hphi, u3ehi0]
                                · linarith only [h1805, h1808, h2040, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h0, h1807, h2019, hlam]
                  · linarith only [h0, h1806, h2018, hlam]
                · linarith only [h0, h1805, h2017, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2046 | h2046
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2047 | h2047
            · linarith only [h1805, h1807, h2047, hlam]
            · linarith only [h2046, h2047, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2050 | h2050
            · linarith only [h2046, h2050, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2052 | h2052
              · linarith only [h1806, h1807, h2052, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2054 | h2054
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2055 | h2055
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2056 | h2056
                    · linarith only [h1805, h1807, h2056, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2058 | h2058
                      · linarith only [h2046, h2054, h2056, h2058, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2060 | h2060
                        · linarith only [h1805, h1807, h2050, h2054, h2056, h2060, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2062 | h2062
                          · linarith only [h1805, h2058, h2062, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2064 | h2064
                            · linarith only [h1334, h1806, h2060, h2062, h2064, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h1806, h2056, h2062, h2064, hc35, hlam, hphi, u3ehi2]
                  · linarith only [h0, h1806, h2055, hlam]
                · linarith only [h0, h1805, h2054, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2069 | h2069
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2070 | h2070
          · linarith only [h1805, h1806, h2070, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2072 | h2072
            · linarith only [h2070, h2072, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2074 | h2074
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2075 | h2075
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2076 | h2076
                  · linarith only [h1805, h1806, h2076, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2078 | h2078
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2079 | h2079
                      · linarith only [h2070, h2075, h2076, h2079, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2081 | h2081
                        · linarith only [h1805, h2072, h2079, h2081, hc34, hlam, hphi, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2083 | h2083
                          · linarith only [h1805, h2079, h2083, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h0, h1805, h2076, h2083, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h2069, h2078, hlam]
                · linarith only [h0, h1805, h2075, hlam]
              · linarith only [h1805, h1806, h2074, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2089 | h2089
          · linarith only [h1805, h1806, h2089, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2091 | h2091
            · linarith only [h2089, h2091, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2093 | h2093
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2094 | h2094
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2095 | h2095
                  · linarith only [h1805, h1806, h2095, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2097 | h2097
                    · linarith only [h1805, h2069, h2095, h2097, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2099 | h2099
                      · linarith only [h2089, h2094, h2095, h2099, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2101 | h2101
                        · linarith only [h1805, h2069, h2091, h2099, h2101, hc34, hlam, hphi, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2103 | h2103
                          · linarith only [h1805, h2099, h2103, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h0, h1805, h2095, h2103, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h1805, h2094, hlam]
              · linarith only [h1805, h1806, h2093, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2108 | h2108
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2109 | h2109
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2110 | h2110
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2111 | h2111
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2112 | h2112
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2113 | h2113
                · linarith only [h1805, h2109, h2113, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2115 | h2115
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2116 | h2116
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2117 | h2117
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2118 | h2118
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2119 | h2119
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2120 | h2120
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2121 | h2121
                              · linarith only [h0, h2108, h2113, h2121, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h1526, h2112, h2113, h2115, h2119, h2121, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h2109, h2113, h2120, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h2108, h2110, h2112, h2113, h2119, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h1334, h1805, h2108, h2111, h2112, h2118, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h1334, h2110, h2117, hlam]
                    · linarith only [h0, h2109, h2116, hlam]
                  · linarith only [h0, h2108, h2115, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2130 | h2130
                · linarith only [h1805, h2109, h2130, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2132 | h2132
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2133 | h2133
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2134 | h2134
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2135 | h2135
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2136 | h2136
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2137 | h2137
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2138 | h2138
                              · linarith only [h2108, h2112, h2138, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2140 | h2140
                                · linarith only [h2108, h2112, h2136, h2140, hlam]
                                · rcases h0bigk with h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c | h2142c
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h0, hlam, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1334, hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1526, hlam, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1712, hlam, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h0, h2130, hc01, hc23, hlam, hphi, ht12, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1805, hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h0, h2108, h2130, h2136, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h0, h2108, h2112, h2130, h2136, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1334, hc01, hc13, hlam, hphi, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1805, hc02, hc23, hlam, hphi, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1805, h2108, h2136, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1805, h2108, h2112, h2136, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2142_1, u3ehi3]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h2112, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h2108, hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h2110, hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h2112, hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h1712, hc01, hc15, hlam, hphi, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h2109, hlam, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h2111, hlam, p2142_0]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [h0, h2109, h2130, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2142_1]
                                  · have p2142_0 := h2142c.1
                                    have p2142_1 := h2142c.2.1
                                    have p2142_2 := h2142c.2.2.1
                                    have p2142_3 := h2142c.2.2.2
                                    linarith only [hlam, p2142_0]
                            · linarith only [h0, h2109, h2130, h2137, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h2109, h2110, h2130, h2136, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · linarith only [h1334, h1805, h2109, h2111, h2135, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h1334, h2110, h2112, h2134, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h0, h2109, h2133, hlam]
                  · linarith only [h0, h2108, h2132, hlam]
            · linarith only [h2110, h2111, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1805, h2108, h2110, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2176 | h2176
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2177 | h2177
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2178 | h2178
              · linarith only [h2108, h2109, h2178, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2180 | h2180
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2181 | h2181
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2182 | h2182
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2183 | h2183
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2184 | h2184
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2185 | h2185
                          · linarith only [h1805, h2108, h2180, h2185, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1805, h2108, h2176, h2185, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h1805, h2177, h2180, h2184, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1805, h2108, h2176, h2180, h2183, hlam]
                    · linarith only [h1805, h2180, h2182, hc02, hc25, hlam, hphi]
                  · linarith only [h1805, h2108, h2176, h2180, h2181, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2192 | h2192
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2193 | h2193
                    · linarith only [h2109, h2180, h2193, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2195 | h2195
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2196 | h2196
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2197 | h2197
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2198 | h2198
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2199 | h2199
                              · linarith only [h2108, h2109, h2178, h2199, hlam]
                              · linarith only [h0, h2108, h2193, h2197, h2199, hc45, hlam, hphi, ht34, u3ehi3]
                            · linarith only [h1805, h2108, h2177, h2197, h2198, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1334, h2177, h2180, h2197, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h1334, h2177, h2196, hlam]
                      · linarith only [h1334, h2177, h2195, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h2108, h2192, hlam]
            · linarith only [h2176, h2177, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1805, h2108, h2176, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2209 | h2209
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2210 | h2210
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2211 | h2211
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2212 | h2212
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2213 | h2213
                · linarith only [h1805, h2209, h2213, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2215 | h2215
                  · linarith only [h2108, h2209, h2215, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2217 | h2217
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2218 | h2218
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2219 | h2219
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2220 | h2220
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2221 | h2221
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2222 | h2222
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2223 | h2223
                                · rcases h0bigk with h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c | h2224c
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [hlam, p2224_0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h0, hlam, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1334, hlam, p2224_0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1526, hlam, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1712, hlam, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h0, h2215, h2220, hc01, hc23, hlam, hphi, ht12, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [hlam, p2224_0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1805, hlam, p2224_0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h2108, hlam, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [hc02, hlam, hphi, ht0b, ht5b, p2224_1, u5ehi0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1334, hc01, hc13, hlam, hphi, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1805, hc02, hc23, hlam, hphi, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [hlam, p2224_0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1526, h1805, hc01, hc23, hlam, hphi, ht12, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1805, h2209, h2221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u3ehi4]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1526, hc01, hc14, hlam, hphi, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h2108, h2209, h2220, h2221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u3ehi4]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h2210, hlam, p2224_0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [hlam, p2224_0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h2108, h2209, h2220, h2221, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2224_1, u3ehi4]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h1712, h2215, h2217, h2220, hc01, hc23, hlam, hphi, ht12, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h2209, hlam, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h2211, hlam, p2224_0]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [h2212, hlam, p2224_1]
                                  · have p2224_0 := h2224c.1
                                    have p2224_1 := h2224c.2.1
                                    have p2224_2 := h2224c.2.2.1
                                    have p2224_3 := h2224c.2.2.2
                                    linarith only [hlam, p2224_0]
                                · linarith only [h0, h2209, h2215, h2220, h2222, h2223, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h2209, h2215, h2222, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                            · linarith only [h0, h2209, h2215, h2220, h2221, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h2209, h2210, h2213, h2220, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · linarith only [h1334, h2210, h2219, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1334, h2210, h2218, hlam]
                    · linarith only [h0, h2209, h2217, hlam]
              · linarith only [h2108, h2209, h2212, hlam]
            · linarith only [h2210, h2211, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2259 | h2259
            · linarith only [h2210, h2259, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1805, h2209, h2259, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2262 | h2262
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2263 | h2263
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2264 | h2264
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2265 | h2265
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2266 | h2266
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2267 | h2267
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2268 | h2268
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2269 | h2269
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2270 | h2270
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2271 | h2271
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2272 | h2272
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2273 | h2273
                                · linarith only [h1805, h2262, h2265, h2273, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · linarith only [h1805, h2262, h2264, h2265, h2273, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h1805, h2108, h2263, h2264, h2265, h2272, hc01, hc12, hlam, hphi]
                            · linarith only [h1805, h2262, h2271, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1805, h2262, h2270, hlam]
                        · linarith only [h1805, h2263, h2265, h2269, hlam]
                      · linarith only [h1805, h2262, h2265, h2268, hlam]
                    · linarith only [h1805, h2262, h2265, h2267, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1805, h2262, h2265, h2266, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2283 | h2283
                  · linarith only [h0, h2108, h2265, h2283, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2285 | h2285
                    · linarith only [h0, h2209, h2265, h2285, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2287 | h2287
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2288 | h2288
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2289 | h2289
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2290 | h2290
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2291 | h2291
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2292 | h2292
                                · rcases h0bigk with h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h0, hlam, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1334, hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1526, hlam, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1712, hlam, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h0, h2285, h2289, h2291, hc01, hc23, hlam, hphi, ht12, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1805, hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h2108, hlam, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h2209, hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1334, hc01, hc13, hlam, hphi, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1805, hc02, hc23, hlam, hphi, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1805, h2262, h2292, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2293_1, u5ehi4]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1805, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2293_1, u5ehi0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1526, hc01, hc14, hlam, hphi, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h0, h2108, h2289, hc01, hc23, hlam, hphi, ht12, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h2262, hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h2108, h2263, h2289, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2293_1, u3ehi4]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h1712, hc01, hc15, hlam, hphi, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h0, h2209, h2289, h2291, hc01, hc23, hlam, hphi, ht12, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h2263, hlam, p2293_0]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [h2264, hlam, p2293_1]
                                  · have p2293_0 := h2293c.1
                                    have p2293_1 := h2293c.2.1
                                    have p2293_2 := h2293c.2.2.1
                                    have p2293_3 := h2293c.2.2.2
                                    linarith only [hlam, p2293_0]
                                · rcases h0bigk with h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h0, hlam, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1334, hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1526, hlam, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1712, hlam, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h0, h2285, h2289, h2291, hc01, hc23, hlam, hphi, ht12, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1805, hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h2108, hlam, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h2209, hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1334, h2265, hc01, hc23, hlam, hphi, ht12, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1334, h2265, hc02, hc23, hlam, hphi, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1334, h2264, h2265, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2319_1, u5ehi0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1334, h2265, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2319_1, u5ehi0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1526, h2283, h2289, hc01, hc23, hlam, hphi, ht12, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h0, h1526, h2283, h2289, hc01, hc23, hlam, hphi, ht12, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h2262, hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1526, h2263, h2283, h2289, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2319_1, u3ehi4]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h1712, h2285, h2289, h2291, hc01, hc23, hlam, hphi, ht12, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h0, h1712, h2285, h2289, h2291, hc01, hc23, hlam, hphi, ht12, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h2263, hlam, p2319_0]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [h2264, hlam, p2319_1]
                                  · have p2319_0 := h2319c.1
                                    have p2319_1 := h2319c.2.1
                                    have p2319_2 := h2319c.2.2.1
                                    have p2319_3 := h2319c.2.2.2
                                    linarith only [hlam, p2319_0]
                              · linarith only [h1526, h2264, h2283, h2291, hlam]
                            · linarith only [h0, h2283, h2289, h2290, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h1334, h1805, h2262, h2289, hc01, hc13, hlam, hphi]
                        · linarith only [h1334, h2263, h2288, hlam]
                      · linarith only [h1334, h2262, h2287, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2350 | h2350
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2351 | h2351
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2352 | h2352
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2353 | h2353
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2354 | h2354
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2355 | h2355
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2356 | h2356
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2357 | h2357
                              · linarith only [h2262, h2264, h2351, h2357, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2359 | h2359
                                · linarith only [h0, h2108, h2357, h2359, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases h0bigk with h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h0, hlam, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1334, hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1526, hlam, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1712, hlam, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h2108, hc01, hc24, hlam, hphi, ht12, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1805, hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h2108, hlam, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h2209, hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1805, h2350, hc01, hc12, hlam, hphi, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1805, h2350, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1805, h2350, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1805, h2350, hc12, hlam, hphi, ht01, ht0b, ht5b, p2361_1, u5ehi0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1526, h2353, hc01, hc13, hlam, hphi, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h0, h2108, h2357, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h2262, hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h2264, hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h1712, hc01, hc15, hlam, hphi, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h0, h2209, h2350, h2356, hc01, hc12, hlam, hphi, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h2263, hlam, p2361_0]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [h2209, h2350, h2356, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2361_1]
                                  · have p2361_0 := h2361c.1
                                    have p2361_1 := h2361c.2.1
                                    have p2361_2 := h2361c.2.2.1
                                    have p2361_3 := h2361c.2.2.2
                                    linarith only [hlam, p2361_0]
                            · linarith only [h1805, h2263, h2356, hlam]
                          · linarith only [h1805, h2263, h2355, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h1805, h2263, h2350, h2354, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1805, h2262, h2350, h2353, hlam]
                    · linarith only [h1805, h2263, h2350, h2352, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h1805, h2262, h2350, h2351, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2393 | h2393
                  · linarith only [h0, h2108, h2350, h2393, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2395 | h2395
                    · linarith only [h0, h2209, h2350, h2395, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2397 | h2397
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2398 | h2398
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2399 | h2399
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2400 | h2400
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2401 | h2401
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2402 | h2402
                                · linarith only [h1334, h1526, h2262, h2264, h2402, hc01, hc13, hlam, hphi]
                                · rcases h0bigk with h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c | h2404c
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h0, hlam, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1334, hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1526, hlam, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1712, hlam, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h0, h2395, h2399, h2401, hc01, hc23, hlam, hphi, ht12, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1805, hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h2108, hlam, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h2209, hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1334, h2350, hc01, hc23, hlam, hphi, ht12, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1334, h2350, hc02, hc23, hlam, hphi, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1334, h2262, h2350, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2404_1, u3ehi3]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1334, h2350, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2404_1, u5ehi0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h2264, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h0, h2264, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h2262, hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h2264, hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1712, h2395, h2399, h2401, hc01, hc23, hlam, hphi, ht12, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h0, h1712, h2395, h2399, h2401, hc01, hc23, hlam, hphi, ht12, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h2263, hlam, p2404_0]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [h1526, h1712, h2395, h2399, h2401, hc01, hc23, hlam, hphi, ht12, p2404_1]
                                  · have p2404_0 := h2404c.1
                                    have p2404_1 := h2404c.2.1
                                    have p2404_2 := h2404c.2.2.1
                                    have p2404_3 := h2404c.2.2.2
                                    linarith only [hlam, p2404_0]
                              · linarith only [h0, h2393, h2401, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h1334, h2262, h2350, h2400, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1334, h2262, h2350, h2399, hlam]
                        · linarith only [h1334, h2263, h2398, hlam]
                      · linarith only [h1334, h2262, h2397, hlam]
            · linarith only [h2262, h2263, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2436 | h2436
            · linarith only [h2262, h2436, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2438 | h2438
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2439 | h2439
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2440 | h2440
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2441 | h2441
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2442 | h2442
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2443 | h2443
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2444 | h2444
                          · linarith only [h2262, h2439, h2444, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h0, h1805, h2439, h2442, h2444, hc01, hc12, hlam, hphi]
                        · linarith only [h2442, h2443, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2448 | h2448
                        · linarith only [h2442, h2448, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2450 | h2450
                          · linarith only [h1334, h2442, h2450, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2452 | h2452
                            · linarith only [h2439, h2448, h2452, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2454 | h2454
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2455 | h2455
                                · rcases h0bigk with h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [hlam, p2456_0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h0, hlam, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h1334, hlam, p2456_0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h1526, hlam, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h1712, hlam, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h1805, h2439, hc01, hc13, hlam, hphi, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [hlam, p2456_0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h1805, hlam, p2456_0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2108, hlam, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2209, hlam, p2456_0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h1334, h2448, h2455, hc01, hc34, hlam, hphi, ht12, ht23, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h1805, h2439, h2448, h2455, hc02, hc34, hlam, hphi, ht23, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [hlam, p2456_0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2262, hlam, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2436, hlam, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2108, h2440, hc01, hc14, hlam, hphi, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h0, h2108, h2440, hc01, hc14, hlam, hphi, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2262, hc34, hlam, hphi, p2456_1, u3ehi0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [hlam, p2456_0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2262, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2456_1, u5ehi0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h1712, hc01, hc15, hlam, hphi, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h0, h2209, h2440, h2454, hc01, hc14, hlam, hphi, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2436, h2455, hc34, hlam, hphi, p2456_1, u3ehi0]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [h2438, hlam, p2456_1]
                                  · have p2456_0 := h2456c.1
                                    have p2456_1 := h2456c.2.1
                                    have p2456_2 := h2456c.2.2.1
                                    have p2456_3 := h2456c.2.2.2
                                    linarith only [hlam, p2456_0]
                                · linarith only [h2108, h2438, h2440, h2455, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h2108, h2438, h2454, hlam]
                    · linarith only [h0, h1805, h2439, h2441, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h1805, h2439, h2440, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2486 | h2486
                  · linarith only [h0, h2108, h2439, h2486, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2488 | h2488
                    · linarith only [h0, h2209, h2439, h2488, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2490 | h2490
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2491 | h2491
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2492 | h2492
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2493 | h2493
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2494 | h2494
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2495 | h2495
                                · rcases h0bigk with h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [hlam, p2496_0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h0, hlam, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h1334, hlam, p2496_0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h1526, hlam, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h1712, hlam, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h0, h2488, h2492, h2494, hc01, hc23, hlam, hphi, ht12, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [hlam, p2496_0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h1805, hlam, p2496_0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2108, hlam, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2209, hlam, p2496_0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2436, h2490, h2495, hc01, hc13, hlam, hphi, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2436, h2490, h2495, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [hlam, p2496_0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2262, hlam, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2436, hlam, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h1526, hc01, hc14, hlam, hphi, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h0, h2108, h2492, hc01, hc23, hlam, hphi, ht12, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2262, h2490, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2496_1, u3ehi0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [hlam, p2496_0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2262, h2490, hc13, hlam, hphi, ht01, ht0b, ht5b, p2496_1, u5ehi0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h1712, hc01, hc15, hlam, hphi, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h0, h2209, h2492, h2494, hc01, hc23, hlam, hphi, ht12, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2436, h2490, h2495, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2496_1, u3ehi0]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [h2438, hlam, p2496_1]
                                  · have p2496_0 := h2496c.1
                                    have p2496_1 := h2496c.2.1
                                    have p2496_2 := h2496c.2.2.1
                                    have p2496_3 := h2496c.2.2.2
                                    linarith only [hlam, p2496_0]
                                · linarith only [h2262, h2495, hc45, hlam, hphi, ht34, u3ehi0]
                              · linarith only [h1526, h2438, h2486, h2494, hlam]
                            · linarith only [h2262, h2439, h2490, h2493, hc35, hlam, hphi, u3ehi0]
                          · linarith only [h2439, h2490, h2492, hlam]
                        · linarith only [h2262, h2490, h2491, hc35, hlam, hphi, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2527 | h2527
                        · linarith only [h2490, h2527, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2529 | h2529
                          · linarith only [h0, h2439, h2490, h2529, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2439, h2529, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2532 | h2532
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2533 | h2533
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2534 | h2534
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2535 | h2535
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2536 | h2536
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2537 | h2537
                          · linarith only [h2262, h2532, h2537, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h0, h1805, h2532, h2535, h2537, hc01, hc12, hlam, hphi]
                        · linarith only [h2535, h2536, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2541 | h2541
                        · linarith only [h2535, h2541, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2543 | h2543
                          · linarith only [h1334, h2535, h2543, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2545 | h2545
                            · linarith only [h2532, h2541, h2545, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2547 | h2547
                              · linarith only [h1526, h2438, h2533, h2547, hc01, hc12, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2549 | h2549
                                · linarith only [h0, h2108, h2547, h2549, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h2262, h2549, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h0, h1805, h2532, h2534, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h1805, h2532, h2533, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2554 | h2554
                  · linarith only [h0, h2108, h2532, h2554, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2556 | h2556
                    · linarith only [h0, h2209, h2532, h2556, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2558 | h2558
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2559 | h2559
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2560 | h2560
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2561 | h2561
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2562 | h2562
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2563 | h2563
                                · linarith only [h2262, h2438, h2563, hc34, hlam, hphi, u3ehi0]
                                · linarith only [h2262, h2560, h2562, h2563, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h0, h2554, h2562, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h2532, h2559, h2561, hlam]
                          · linarith only [h2436, h2532, h2558, h2559, h2560, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h2262, h2558, h2559, hc35, hlam, hphi, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2570 | h2570
                        · linarith only [h2558, h2570, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2572 | h2572
                          · linarith only [h1334, h2558, h2572, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2532, h2572, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5150000 in
set_option maxHeartbeats 5150000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1334 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1526 | h1526
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1334 h1526
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1334 h1526

end R2N4
