import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_46S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h567 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 2 3 4 (by decide) (by decide) with h1719 | h1719
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1720 | h1720
    · rcases m.htr 2 4 5 (by decide) (by decide) with h1721 | h1721
      · linarith only [h1721, h563, h567, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h1723 | h1723
        · linarith only [h1719, h1723, h563, h567, hc23, hlam, hphi, u2ehi3]
        · rcases h0bigk with h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [hlam, p1725_0]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h0, hlam, p1725_1]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h451, hlam, p1725_0]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h451, h561, h562, h567, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1725_1]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h451, h561, h562, h563, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1725_1, u2ehi3]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            rcases p1725_3 (m.d 0 1) (by simp) with h1731 | h1731
            · linarith only [h0, h1731, hlam]
            · rcases p1725_3 (m.d 0 2) (by simp) with h1733 | h1733
              · rcases p1725_3 (m.d 0 3) (by simp) with h1734 | h1734
                · linarith only [h1734, h556, hlam]
                · linarith only [h1734, h451, hlam]
              · linarith only [h0, h1733, hlam]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [hlam, p1725_0]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h0, h1720, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1725_1, u3ehi4]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h0, h561, h563, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1725_1, u2ehi3]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h0, h561, h563, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1725_1, u2ehi3]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            rcases p1725_3 (m.d 0 1) (by simp) with h1742 | h1742
            · linarith only [h1742, h451, hlam]
            · rcases p1725_3 (m.d 0 2) (by simp) with h1744 | h1744
              · rcases p1725_3 (m.d 0 3) (by simp) with h1745 | h1745
                · rcases p1725_3 (m.d 0 4) (by simp) with h1746 | h1746
                  · linarith only [h1746, h559, hlam]
                  · linarith only [h0, h1746, h561, h563, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h1745, h451, hlam]
              · linarith only [h0, h1744, hlam]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h556, hlam, p1725_1]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [hlam, p1725_0]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h561, h563, h567, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1725_1, u2ehi3]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h451, h561, h562, h563, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1725_1, u2ehi3]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            rcases p1725_3 (m.d 0 1) (by simp) with h1755 | h1755
            · linarith only [h1755, hlam, p1725_0]
            · rcases p1725_3 (m.d 0 2) (by simp) with h1757 | h1757
              · rcases p1725_3 (m.d 0 3) (by simp) with h1758 | h1758
                · rcases p1725_3 (m.d 0 4) (by simp) with h1759 | h1759
                  · rcases p1725_3 (m.d 0 5) (by simp) with h1760 | h1760
                    · linarith only [h1760, h561, hlam]
                    · linarith only [h1760, h561, h563, h567, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1725_1, u2ehi3]
                  · linarith only [h1759, hlam, p1725_0]
                · linarith only [h1758, h451, hlam]
              · linarith only [h0, h1757, hlam]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h557, hlam, p1725_0]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h559, hlam, p1725_0]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [hlam, p1725_0]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h451, h559, h561, h562, h563, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1725_1, u2ehi3]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            rcases p1725_3 (m.d 0 1) (by simp) with h1770 | h1770
            · linarith only [h1770, hlam, p1725_0]
            · rcases p1725_3 (m.d 0 2) (by simp) with h1772 | h1772
              · rcases p1725_3 (m.d 0 3) (by simp) with h1773 | h1773
                · rcases p1725_3 (m.d 0 4) (by simp) with h1774 | h1774
                  · rcases p1725_3 (m.d 0 5) (by simp) with h1775 | h1775
                    · rcases h0emin with h1776 | h1776 | h1776 | h1776 | h1776
                      · linarith only [h1776, hc05, hlam, p1725_1]
                      · rcases h3bigk with h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c | h1778c
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h451, hlam, p1778_1]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h1720, h1723, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1778_1, u3ehi3]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          rcases p1778_3 (m.d 0 3) (by simp) with h1782 | h1782
                          · rcases p1778_3 (m.d 1 3) (by simp) with h1783 | h1783
                            · rcases p1778_3 (m.d 2 3) (by simp) with h1784 | h1784
                              · linarith only [h1784, h556, hlam]
                              · linarith only [h1719, h1784, hlam]
                            · linarith only [h1783, h565, hlam]
                          · linarith only [h1782, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          rcases p1778_3 (m.d 0 3) (by simp) with h1789 | h1789
                          · rcases p1778_3 (m.d 1 3) (by simp) with h1790 | h1790
                            · rcases p1778_3 (m.d 2 3) (by simp) with h1791 | h1791
                              · linarith only [h1791, h556, hlam]
                              · linarith only [h1720, h1791, hlam]
                            · linarith only [h1790, h566, hlam]
                          · linarith only [h1789, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h559, h561, h562, hc01, hc12, hlam, hphi, p1725_1, p1778_1]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h1720, h1723, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1778_1, u3ehi3]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          rcases p1778_3 (m.d 0 3) (by simp) with h1799 | h1799
                          · linarith only [h1799, h451, hlam]
                          · linarith only [h1799, h559, hlam]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          rcases p1778_3 (m.d 0 3) (by simp) with h1802 | h1802
                          · linarith only [h1802, h451, hlam]
                          · linarith only [h1802, h560, hlam]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h556, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h562, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1778_1, u3ehi3]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h0, h1723, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1778_1, u3ehi3]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h559, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h565, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h1719, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h1723, hlam, p1778_1]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h560, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h566, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [h1720, hlam, p1778_0]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [hc35, hlam, hphi, p1778_1, u3ehi3]
                        · have p1778_0 := h1778c.1
                          have p1778_1 := h1778c.2.1
                          have p1778_2 := h1778c.2.2.1
                          have p1778_3 := h1778c.2.2.2
                          linarith only [hlam, p1778_0]
                      · rcases h3bigk with h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h451, hlam, p1820_1]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h1720, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1820_1, u3ehi4]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          rcases p1820_3 (m.d 0 3) (by simp) with h1824 | h1824
                          · rcases p1820_3 (m.d 1 3) (by simp) with h1825 | h1825
                            · rcases p1820_3 (m.d 2 3) (by simp) with h1826 | h1826
                              · linarith only [h1826, h556, hlam]
                              · linarith only [h1719, h1826, hlam]
                            · linarith only [h1825, h565, hlam]
                          · linarith only [h1824, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          rcases p1820_3 (m.d 0 3) (by simp) with h1831 | h1831
                          · rcases p1820_3 (m.d 1 3) (by simp) with h1832 | h1832
                            · rcases p1820_3 (m.d 2 3) (by simp) with h1833 | h1833
                              · linarith only [h1833, h556, hlam]
                              · linarith only [h1720, h1833, hlam]
                            · linarith only [h1832, h566, hlam]
                          · linarith only [h1831, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h1776, h562, hc12, hlam, ht01, p1820_1]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h1719, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1820_1, u3ehi3]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          rcases p1820_3 (m.d 0 3) (by simp) with h1841 | h1841
                          · linarith only [h1841, h451, hlam]
                          · linarith only [h1841, h559, hlam]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          rcases p1820_3 (m.d 0 3) (by simp) with h1844 | h1844
                          · linarith only [h1844, h451, hlam]
                          · linarith only [h1844, h560, hlam]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h556, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h562, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1820_1, u3ehi3]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h0, h1723, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1820_1, u3ehi3]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h559, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h565, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h1719, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h1723, hlam, p1820_1]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h560, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h566, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [h1720, hlam, p1820_0]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [hc35, hlam, hphi, p1820_1, u3ehi3]
                        · have p1820_0 := h1820c.1
                          have p1820_1 := h1820c.2.1
                          have p1820_2 := h1820c.2.2.1
                          have p1820_3 := h1820c.2.2.2
                          linarith only [hlam, p1820_0]
                      · rcases h3bigk with h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c | h1862c
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h451, hlam, p1862_1]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h1720, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1862_1, u3ehi4]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          rcases p1862_3 (m.d 0 3) (by simp) with h1866 | h1866
                          · rcases p1862_3 (m.d 1 3) (by simp) with h1867 | h1867
                            · rcases p1862_3 (m.d 2 3) (by simp) with h1868 | h1868
                              · linarith only [h1868, h556, hlam]
                              · linarith only [h1719, h1868, hlam]
                            · linarith only [h1867, h565, hlam]
                          · linarith only [h1866, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          rcases p1862_3 (m.d 0 3) (by simp) with h1873 | h1873
                          · rcases p1862_3 (m.d 1 3) (by simp) with h1874 | h1874
                            · rcases p1862_3 (m.d 2 3) (by simp) with h1875 | h1875
                              · linarith only [h1875, h556, hlam]
                              · linarith only [h1720, h1875, hlam]
                            · linarith only [h1874, h566, hlam]
                          · linarith only [h1873, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h1720, h1723, h556, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1862_1, u3ehi3]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h1720, h1723, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1862_1, u3ehi3]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          rcases p1862_3 (m.d 0 3) (by simp) with h1883 | h1883
                          · linarith only [h1883, h451, hlam]
                          · linarith only [h1883, h559, hlam]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          rcases p1862_3 (m.d 0 3) (by simp) with h1886 | h1886
                          · linarith only [h1886, h451, hlam]
                          · linarith only [h1886, h560, hlam]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h556, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h562, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1862_1, u3ehi3]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h0, h1723, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1862_1, u3ehi3]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h559, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h565, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h1719, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h1723, hlam, p1862_1]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h560, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h566, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [h1720, hlam, p1862_0]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [hc35, hlam, hphi, p1862_1, u3ehi3]
                        · have p1862_0 := h1862c.1
                          have p1862_1 := h1862c.2.1
                          have p1862_2 := h1862c.2.2.1
                          have p1862_3 := h1862c.2.2.2
                          linarith only [hlam, p1862_0]
                      · rcases h3bigk with h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c | h1904c
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h451, hlam, p1904_1]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h1720, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1904_1, u3ehi4]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          rcases p1904_3 (m.d 0 3) (by simp) with h1908 | h1908
                          · rcases p1904_3 (m.d 1 3) (by simp) with h1909 | h1909
                            · rcases p1904_3 (m.d 2 3) (by simp) with h1910 | h1910
                              · linarith only [h1910, h556, hlam]
                              · linarith only [h1719, h1910, hlam]
                            · linarith only [h1909, h565, hlam]
                          · linarith only [h1908, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          rcases p1904_3 (m.d 0 3) (by simp) with h1915 | h1915
                          · rcases p1904_3 (m.d 1 3) (by simp) with h1916 | h1916
                            · rcases p1904_3 (m.d 2 3) (by simp) with h1917 | h1917
                              · linarith only [h1917, h556, hlam]
                              · linarith only [h1720, h1917, hlam]
                            · linarith only [h1916, h566, hlam]
                          · linarith only [h1915, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h1720, h1723, h556, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1904_1, u3ehi3]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h1720, h1723, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1904_1, u3ehi3]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          rcases p1904_3 (m.d 0 3) (by simp) with h1925 | h1925
                          · linarith only [h1925, h451, hlam]
                          · linarith only [h1925, h559, hlam]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          rcases p1904_3 (m.d 0 3) (by simp) with h1928 | h1928
                          · linarith only [h1928, h451, hlam]
                          · linarith only [h1928, h560, hlam]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h556, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h562, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1904_1, u3ehi3]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h0, h1723, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1904_1, u3ehi3]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h559, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h565, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h1719, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h1723, hlam, p1904_1]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h560, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h566, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [h1720, hlam, p1904_0]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [hc35, hlam, hphi, p1904_1, u3ehi3]
                        · have p1904_0 := h1904c.1
                          have p1904_1 := h1904c.2.1
                          have p1904_2 := h1904c.2.2.1
                          have p1904_3 := h1904c.2.2.2
                          linarith only [hlam, p1904_0]
                    · linarith only [h1775, hlam, p1725_0]
                  · linarith only [h0, h1774, h561, h563, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h1773, h451, hlam]
              · linarith only [h0, h1772, hlam]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h558, hlam, p1725_1]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h560, hlam, p1725_0]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [h561, hlam, p1725_1]
          · have p1725_0 := h1725c.1
            have p1725_1 := h1725c.2.1
            have p1725_2 := h1725c.2.2.1
            have p1725_3 := h1725c.2.2.2
            linarith only [hlam, p1725_0]
    · linarith only [h1719, h1720, h561, h566, h567, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
  · linarith only [h1719, h451, h559, h561, h562, h565, h567, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566 h567
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566 h567

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h451, h559, h566, hc35, hlam, hphi, u3ehi3]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 3 5 (by decide) (by decide) with h566 | h566
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h451, h559, h565, hlam]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 3 4 (by decide) (by decide) with h565 | h565
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h0, h558, h564, hlam]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 5 (by decide) (by decide) with h564 | h564
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h0, h556, h563, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 4 (by decide) (by decide) with h563 | h563
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h0, h556, h562, hlam]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562

end R2N4
