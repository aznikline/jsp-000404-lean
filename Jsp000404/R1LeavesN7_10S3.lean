import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S1
import Jsp000404.R1LeavesN7_10S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x1_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1008 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1124 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1181 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 4 5 (by decide) (by decide) with h1687 | h1687
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1688 | h1688
    · rcases m.htr 2 3 5 (by decide) (by decide) with h1689 | h1689
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1690 | h1690
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1691 | h1691
          · rcases h2bigk with h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1181, h1688, h2, h7, hlam, p1692_2]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1181, h1688, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1692_1]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              rcases p1692_3 (m.d 0 2) (by simp) with h1696 | h1696
              · rcases p1692_3 (m.d 1 2) (by simp) with h1697 | h1697
                · linarith only [h0, h1697, hlam]
                · rcases p1692_3 (m.d 2 3) (by simp) with h1699 | h1699
                  · linarith only [h1699, h2, hlam]
                  · linarith only [h1688, h1699, hlam]
              · linarith only [h1696, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              rcases p1692_3 (m.d 0 2) (by simp) with h1703 | h1703
              · rcases p1692_3 (m.d 1 2) (by simp) with h1704 | h1704
                · linarith only [h0, h1704, hlam]
                · rcases p1692_3 (m.d 2 3) (by simp) with h1706 | h1706
                  · linarith only [h1706, h2, hlam]
                  · linarith only [h1689, h1706, hlam]
              · linarith only [h1703, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h0, hlam, p1692_1]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h7, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1008, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1124, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h2, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              rcases p1692_3 (m.d 0 2) (by simp) with h1716 | h1716
              · rcases p1692_3 (m.d 1 2) (by simp) with h1717 | h1717
                · linarith only [h1717, hlam, p1692_0]
                · rcases p1692_3 (m.d 2 3) (by simp) with h1719 | h1719
                  · rcases p1692_3 (m.d 2 4) (by simp) with h1720 | h1720
                    · linarith only [h1688, h1720, hlam]
                    · linarith only [h1008, h1720, hlam]
                  · linarith only [h1719, hlam, p1692_0]
              · linarith only [h0, h1716, hlam]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1181, h1688, h7, hc12, hc23, hlam, hphi, p1692_1]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h0, h1124, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1692_1]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h3, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              rcases p1692_3 (m.d 0 2) (by simp) with h1729 | h1729
              · rcases p1692_3 (m.d 1 2) (by simp) with h1730 | h1730
                · linarith only [h1730, hlam, p1692_0]
                · rcases p1692_3 (m.d 2 3) (by simp) with h1732 | h1732
                  · rcases p1692_3 (m.d 2 4) (by simp) with h1733 | h1733
                    · rcases p1692_3 (m.d 2 5) (by simp) with h1734 | h1734
                      · linarith only [h1690, h1734, hlam]
                      · linarith only [h1124, h1734, hlam]
                    · linarith only [h1733, hlam, p1692_0]
                  · linarith only [h1732, h7, hlam]
              · linarith only [h0, h1729, hlam]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1688, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1124, hc12, hc24, hlam, hphi, p1692_1]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h4, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              rcases p1692_3 (m.d 0 2) (by simp) with h1744 | h1744
              · rcases p1692_3 (m.d 1 2) (by simp) with h1745 | h1745
                · linarith only [h1745, hlam, p1692_0]
                · rcases p1692_3 (m.d 2 3) (by simp) with h1747 | h1747
                  · rcases p1692_3 (m.d 2 4) (by simp) with h1748 | h1748
                    · rcases p1692_3 (m.d 2 5) (by simp) with h1749 | h1749
                      · rcases h4bigk with h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h0, h1687, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h0, h1008, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h0, h1181, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          rcases p1750_3 (m.d 0 4) (by simp) with h1755 | h1755
                          · rcases p1750_3 (m.d 1 4) (by simp) with h1756 | h1756
                            · linarith only [h1, h1756, hlam]
                            · linarith only [h1687, h1756, hlam]
                          · linarith only [h1755, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1008, hlam, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1181, hlam, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h3, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h0, h1181, h1688, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h0, h1688, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h5, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1687, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1688, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h0, h1688, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1750_1]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h6, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1687, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1690, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [h1691, hlam, p1750_0]
                        · have p1750_0 := h1750c.1
                          have p1750_1 := h1750c.2.1
                          have p1750_2 := h1750c.2.2.1
                          have p1750_3 := h1750c.2.2.2
                          linarith only [hlam, p1750_0]
                      · linarith only [h1749, hlam, p1692_0]
                    · linarith only [h1008, h1748, hlam]
                  · linarith only [h1747, h7, hlam]
              · linarith only [h0, h1744, hlam]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1689, hlam, p1692_0]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [h1690, hlam, p1692_1]
            · have p1692_0 := h1692c.1
              have p1692_1 := h1692c.2.1
              have p1692_2 := h1692c.2.2.1
              have p1692_3 := h1692c.2.2.2
              linarith only [hlam, p1692_0]
          · linarith only [h1, h1181, h1687, h1691, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h1181, h1687, h1688, h1690, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h1181, h1688, h1689, h7, hc12, hc35, hlam, hphi, ht23]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h1790 | h1790
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1791 | h1791
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1792 | h1792
          · rcases h2bigk with h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c | h1793c
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h1124, h1688, h1790, h2, h5, hlam, p1793_2]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              rcases p1793_3 (m.d 0 2) (by simp) with h1796 | h1796
              · rcases p1793_3 (m.d 1 2) (by simp) with h1797 | h1797
                · linarith only [h0, h1797, hlam]
                · rcases p1793_3 (m.d 2 3) (by simp) with h1799 | h1799
                  · linarith only [h1799, hlam, p1793_0]
                  · rcases p1793_3 (m.d 2 4) (by simp) with h1801 | h1801
                    · linarith only [h1801, h3, hlam]
                    · linarith only [h1688, h1801, hlam]
              · linarith only [h1796, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              rcases p1793_3 (m.d 0 2) (by simp) with h1805 | h1805
              · rcases p1793_3 (m.d 1 2) (by simp) with h1806 | h1806
                · linarith only [h0, h1806, hlam]
                · rcases p1793_3 (m.d 2 3) (by simp) with h1808 | h1808
                  · linarith only [h1808, h2, hlam]
                  · rcases p1793_3 (m.d 2 4) (by simp) with h1810 | h1810
                    · linarith only [h1810, hlam, p1793_0]
                    · rcases p1793_3 (m.d 2 5) (by simp) with h1812 | h1812
                      · linarith only [h1812, h4, hlam]
                      · rcases h4bigk with h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h0, h1687, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h2, h5, hlam, p1793_2, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h0, h1688, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          rcases p1814_3 (m.d 0 4) (by simp) with h1819 | h1819
                          · rcases p1814_3 (m.d 1 4) (by simp) with h1820 | h1820
                            · linarith only [h1, h1820, hlam]
                            · linarith only [h1687, h1820, hlam]
                          · linarith only [h1819, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1008, hlam, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1181, hlam, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h3, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1793_1, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1688, hlam, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p1793_1, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h5, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1687, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h6, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1687, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1791, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1792, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
              · linarith only [h1805, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              rcases p1793_3 (m.d 0 2) (by simp) with h1845 | h1845
              · rcases p1793_3 (m.d 1 2) (by simp) with h1846 | h1846
                · linarith only [h0, h1846, hlam]
                · rcases p1793_3 (m.d 2 3) (by simp) with h1848 | h1848
                  · linarith only [h1848, h2, hlam]
                  · linarith only [h1790, h1848, hlam]
              · linarith only [h1845, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h0, hlam, p1793_1]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h7, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h1008, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h1124, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h2, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h0, h1688, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1793_1]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h1688, hlam, p1793_1]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h0, h1688, h2, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p1793_1]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h3, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              rcases p1793_3 (m.d 0 2) (by simp) with h1863 | h1863
              · rcases p1793_3 (m.d 1 2) (by simp) with h1864 | h1864
                · linarith only [h1864, hlam, p1793_0]
                · rcases p1793_3 (m.d 2 3) (by simp) with h1866 | h1866
                  · linarith only [h1688, h1866, hlam]
                  · linarith only [h1866, h7, hlam]
              · linarith only [h0, h1863, hlam]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h0, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1793_1]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h0, h1124, h1688, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1793_1]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h4, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h0, h1688, h1790, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1793_1]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h1790, hlam, p1793_0]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [h1791, hlam, p1793_1]
            · have p1793_0 := h1793c.1
              have p1793_1 := h1793c.2.1
              have p1793_2 := h1793c.2.2.1
              have p1793_3 := h1793c.2.2.2
              linarith only [hlam, p1793_0]
          · linarith only [h1, h1687, h1688, h1792, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h1, h1008, h1687, h1791, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1880 | h1880
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1881 | h1881
          · rcases h2bigk with h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h1790, h1881, h2, h5, h7, hlam, p1882_2]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              rcases p1882_3 (m.d 0 2) (by simp) with h1885 | h1885
              · rcases p1882_3 (m.d 1 2) (by simp) with h1886 | h1886
                · linarith only [h0, h1886, hlam]
                · rcases p1882_3 (m.d 2 3) (by simp) with h1888 | h1888
                  · linarith only [h1888, hlam, p1882_0]
                  · rcases p1882_3 (m.d 2 4) (by simp) with h1890 | h1890
                    · linarith only [h1890, h3, hlam]
                    · linarith only [h1688, h1890, hlam]
              · linarith only [h1885, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              rcases p1882_3 (m.d 0 2) (by simp) with h1894 | h1894
              · rcases p1882_3 (m.d 1 2) (by simp) with h1895 | h1895
                · linarith only [h0, h1895, hlam]
                · rcases p1882_3 (m.d 2 3) (by simp) with h1897 | h1897
                  · linarith only [h1897, h2, hlam]
                  · rcases p1882_3 (m.d 2 4) (by simp) with h1899 | h1899
                    · linarith only [h1899, hlam, p1882_0]
                    · rcases p1882_3 (m.d 2 5) (by simp) with h1901 | h1901
                      · linarith only [h1901, h4, hlam]
                      · rcases h4bigk with h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h0, h1687, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h2, h5, hlam, p1882_2, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h0, h1790, h1881, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          rcases p1903_3 (m.d 0 4) (by simp) with h1908 | h1908
                          · rcases p1903_3 (m.d 1 4) (by simp) with h1909 | h1909
                            · linarith only [h1, h1909, hlam]
                            · linarith only [h1687, h1909, hlam]
                          · linarith only [h1908, hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1, hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1008, hlam, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1181, hlam, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h3, hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1882_1, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1688, hlam, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p1882_1, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h5, hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1687, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h0, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1903_1]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h6, hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1687, hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1880, hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [h1881, hlam, p1903_0]
                        · have p1903_0 := h1903c.1
                          have p1903_1 := h1903c.2.1
                          have p1903_2 := h1903c.2.2.1
                          have p1903_3 := h1903c.2.2.2
                          linarith only [hlam, p1903_0]
              · linarith only [h1894, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              rcases p1882_3 (m.d 0 2) (by simp) with h1934 | h1934
              · rcases p1882_3 (m.d 1 2) (by simp) with h1935 | h1935
                · linarith only [h0, h1935, hlam]
                · rcases p1882_3 (m.d 2 3) (by simp) with h1937 | h1937
                  · linarith only [h1937, h2, hlam]
                  · rcases p1882_3 (m.d 2 4) (by simp) with h1939 | h1939
                    · linarith only [h1939, h3, hlam]
                    · linarith only [h1880, h1939, hlam]
              · linarith only [h1934, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h0, hlam, p1882_1]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h7, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h1008, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h1124, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h2, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h1790, hc12, hc35, hlam, hphi, ht23, p1882_1]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h1688, hlam, p1882_1]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h1790, hlam, p1882_1]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h3, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              rcases p1882_3 (m.d 0 2) (by simp) with h1954 | h1954
              · rcases p1882_3 (m.d 1 2) (by simp) with h1955 | h1955
                · linarith only [h1955, hlam, p1882_0]
                · rcases p1882_3 (m.d 2 3) (by simp) with h1957 | h1957
                  · linarith only [h1688, h1957, hlam]
                  · linarith only [h1957, h7, hlam]
              · linarith only [h0, h1954, hlam]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h0, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1882_1]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h0, h1688, h1790, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1882_1]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h4, hlam, p1882_0]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              rcases p1882_3 (m.d 0 2) (by simp) with h1965 | h1965
              · rcases p1882_3 (m.d 1 2) (by simp) with h1966 | h1966
                · linarith only [h1966, hlam, p1882_0]
                · rcases p1882_3 (m.d 2 3) (by simp) with h1968 | h1968
                  · linarith only [h1790, h1968, hlam]
                  · linarith only [h1968, h7, hlam]
              · linarith only [h0, h1965, hlam]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h7, hc12, hc25, hlam, hphi, p1882_1]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [h1880, hlam, p1882_1]
            · have p1882_0 := h1882c.1
              have p1882_1 := h1882c.2.1
              have p1882_2 := h1882c.2.2.1
              have p1882_3 := h1882c.2.2.2
              linarith only [hlam, p1882_0]
          · linarith only [h1, h1008, h1687, h1688, h1881, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h1008, h1687, h1880, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1977 | h1977
    · rcases m.htr 2 3 5 (by decide) (by decide) with h1978 | h1978
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1979 | h1979
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1980 | h1980
          · linarith only [h0, h1687, h1977, h1980, h2, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1181, h1977, h1979, h1980, h2, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1983 | h1983
          · linarith only [h0, h1008, h1979, h1983, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases h2bigk with h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1181, h1977, h1979, h2, h5, h6, h7, hlam, p1985_2]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1181, h1977, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1985_1]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              rcases p1985_3 (m.d 0 2) (by simp) with h1989 | h1989
              · rcases p1985_3 (m.d 1 2) (by simp) with h1990 | h1990
                · linarith only [h0, h1990, hlam]
                · rcases p1985_3 (m.d 2 3) (by simp) with h1992 | h1992
                  · linarith only [h1992, h2, hlam]
                  · linarith only [h1977, h1992, hlam]
              · linarith only [h1989, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              rcases p1985_3 (m.d 0 2) (by simp) with h1996 | h1996
              · rcases p1985_3 (m.d 1 2) (by simp) with h1997 | h1997
                · linarith only [h0, h1997, hlam]
                · rcases p1985_3 (m.d 2 3) (by simp) with h1999 | h1999
                  · linarith only [h1999, h2, hlam]
                  · linarith only [h1978, h1999, hlam]
              · linarith only [h1996, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h0, hlam, p1985_1]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h7, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1008, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1124, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h2, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              rcases p1985_3 (m.d 0 2) (by simp) with h2009 | h2009
              · rcases p1985_3 (m.d 1 2) (by simp) with h2010 | h2010
                · linarith only [h2010, hlam, p1985_0]
                · rcases p1985_3 (m.d 2 3) (by simp) with h2012 | h2012
                  · rcases p1985_3 (m.d 2 4) (by simp) with h2013 | h2013
                    · linarith only [h1977, h2013, hlam]
                    · linarith only [h1008, h2013, hlam]
                  · linarith only [h2012, hlam, p1985_0]
              · linarith only [h0, h2009, hlam]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1181, h1977, h7, hc12, hc23, hlam, hphi, p1985_1]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h0, h1124, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1985_1]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h3, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1979, h5, h6, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1985_1]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1977, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1979, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h4, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              rcases p1985_3 (m.d 0 2) (by simp) with h2027 | h2027
              · rcases p1985_3 (m.d 1 2) (by simp) with h2028 | h2028
                · linarith only [h2028, hlam, p1985_0]
                · rcases p1985_3 (m.d 2 3) (by simp) with h2030 | h2030
                  · rcases p1985_3 (m.d 2 4) (by simp) with h2031 | h2031
                    · linarith only [h1979, h2031, hlam]
                    · linarith only [h1008, h2031, hlam]
                  · linarith only [h2030, h7, hlam]
              · linarith only [h0, h2027, hlam]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h1978, hlam, p1985_0]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [h0, h1008, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1985_1]
            · have p1985_0 := h1985c.1
              have p1985_1 := h1985c.2.1
              have p1985_2 := h1985c.2.2.1
              have p1985_3 := h1985c.2.2.2
              linarith only [hlam, p1985_0]
      · linarith only [h1181, h1977, h1978, h7, hc12, hc35, hlam, hphi, ht23]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2040 | h2040
      · rcases m.htr 2 4 5 (by decide) (by decide) with h2041 | h2041
        · rcases m.htr 3 4 5 (by decide) (by decide) with h2042 | h2042
          · linarith only [h1181, h1687, h1977, h2040, h2042, h7, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1977, h2040, h2041, h2042, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · linarith only [h1977, h2040, h2041, hlam]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h2046 | h2046
        · rcases m.htr 3 4 5 (by decide) (by decide) with h2047 | h2047
          · rcases h2bigk with h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h1181, h1687, h2046, h3, h7, hlam, p2048_2]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              rcases p2048_3 (m.d 0 2) (by simp) with h2051 | h2051
              · rcases p2048_3 (m.d 1 2) (by simp) with h2052 | h2052
                · linarith only [h0, h2052, hlam]
                · rcases p2048_3 (m.d 2 3) (by simp) with h2054 | h2054
                  · linarith only [h2054, hlam, p2048_0]
                  · rcases p2048_3 (m.d 2 4) (by simp) with h2056 | h2056
                    · linarith only [h2056, h3, hlam]
                    · linarith only [h1977, h2056, hlam]
              · linarith only [h2051, hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h0, h1181, h1687, h2046, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              rcases p2048_3 (m.d 0 2) (by simp) with h2061 | h2061
              · rcases p2048_3 (m.d 1 2) (by simp) with h2062 | h2062
                · linarith only [h0, h2062, hlam]
                · rcases p2048_3 (m.d 2 3) (by simp) with h2064 | h2064
                  · linarith only [h2, h2064, hlam]
                  · rcases p2048_3 (m.d 2 4) (by simp) with h2066 | h2066
                    · linarith only [h2066, h3, hlam]
                    · linarith only [h2046, h2066, hlam]
              · linarith only [h2061, hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h0, hlam, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h7, hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h1008, hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h1124, hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h2, hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h2040, h2047, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h1977, hlam, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h2040, hlam, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h3, hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              rcases p2048_3 (m.d 0 2) (by simp) with h2081 | h2081
              · rcases p2048_3 (m.d 1 2) (by simp) with h2082 | h2082
                · linarith only [h2082, hlam, p2048_0]
                · rcases p2048_3 (m.d 2 3) (by simp) with h2084 | h2084
                  · linarith only [h1977, h2084, hlam]
                  · linarith only [h2084, h7, hlam]
              · linarith only [h0, h2081, hlam]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h0, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h0, h1977, h2, h2040, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h4, hlam, p2048_0]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              rcases p2048_3 (m.d 0 2) (by simp) with h2092 | h2092
              · rcases p2048_3 (m.d 1 2) (by simp) with h2093 | h2093
                · linarith only [h2093, hlam, p2048_0]
                · rcases p2048_3 (m.d 2 3) (by simp) with h2095 | h2095
                  · linarith only [h2040, h2095, hlam]
                  · linarith only [h2095, h7, hlam]
              · linarith only [h0, h2092, hlam]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h7, hc12, hc25, hlam, hphi, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [h2046, hlam, p2048_1]
            · have p2048_0 := h2048c.1
              have p2048_1 := h2048c.2.1
              have p2048_2 := h2048c.2.2.1
              have p2048_3 := h2048c.2.2.2
              linarith only [hlam, p2048_0]
          · linarith only [h0, h1977, h2, h2047, h5, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h2103 | h2103
          · linarith only [h0, h1008, h2, h2046, h2103, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h0, h1977, h2, h2103, h5, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1008 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1124 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 3 4 (by decide) (by decide) with h1181 | h1181
  · exact r1l7_12_24_L_I_H_I_s5_x0_x1_x1_x1_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h1008 h1124 h1181
  · exact r1l7_12_24_L_I_H_I_s5_x0_x1_x1_x1_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h1008 h1124 h1181

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1008 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 5 (by decide) (by decide) with h1124 | h1124
  · exact r1l7_12_24_L_I_H_I_s5_x0_x1_x1_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h1008 h1124
  · exact r1l7_12_24_L_I_H_I_s5_x0_x1_x1_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h1008 h1124

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 4 (by decide) (by decide) with h1008 | h1008
  · exact r1l7_12_24_L_I_H_I_s5_x0_x1_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h1008
  · exact r1l7_12_24_L_I_H_I_s5_x0_x1_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7 h1008

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
  · exact r1l7_12_24_L_I_H_I_s5_x0_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7
  · exact r1l7_12_24_L_I_H_I_s5_x0_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h7

end R2N4
