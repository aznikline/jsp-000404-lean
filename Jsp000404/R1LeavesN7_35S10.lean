import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_35S8
import Jsp000404.R1LeavesN7_35S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1387 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1549 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1606 | h1606
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1607 | h1607
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1608 | h1608
      · linarith only [h0, h1, h1608, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1610 | h1610
        · linarith only [h0, h1387, h1610, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1612 | h1612
          · linarith only [h0, h1549, h1612, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1614 | h1614
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1615 | h1615
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1616 | h1616
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1617 | h1617
                  · rcases h2bigk with h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1549, h1615, h1617, hc12, hc23, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1387, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1549, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, hlam, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1608, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1610, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1612, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1617, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1618_1, u5ehi2]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, h1549, hc12, hc23, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1615, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, h1549, h1615, hc12, hc23, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1616, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1617, hlam, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                  · linarith only [h0, h1, h1387, h1606, h1607, h1617, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1645 | h1645
                  · linarith only [h1615, h1616, h1645, hlam]
                  · linarith only [h0, h1, h1387, h1606, h1607, h1616, h1645, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1, h1606, h1607, h1614, h1615, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1649 | h1649
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1650 | h1650
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1651 | h1651
                  · rcases h2bigk with h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1, hc12, hc23, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1, hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1387, hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1549, hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h0, hlam, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1608, hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1610, hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1612, hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1651, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1652_1, u5ehi2]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h0, h1549, hc12, hc23, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1649, hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h0, h1549, h1649, hc12, hc23, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1650, hlam, p1652_0]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [h1651, hlam, p1652_1]
                    · have p1652_0 := h1652c.1
                      have p1652_1 := h1652c.2.1
                      have p1652_2 := h1652c.2.2.1
                      have p1652_3 := h1652c.2.2.2
                      linarith only [hlam, p1652_0]
                  · linarith only [h1387, h1607, h1651, hlam]
                · linarith only [h1, h1606, h1608, h1614, h1650, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1, h1606, h1649, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1681 | h1681
      · linarith only [h0, h1, h1681, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1683 | h1683
        · linarith only [h0, h1387, h1683, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1685 | h1685
          · linarith only [h0, h1549, h1685, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1687 | h1687
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1688 | h1688
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1689 | h1689
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1690 | h1690
                  · rcases h2bigk with h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1387, h1607, h1688, h1690, hc12, hc23, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1, hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1387, hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1549, hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h0, hlam, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1681, hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1683, hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1685, hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1607, h1690, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h0, h1387, h1607, h1690, hc12, hc23, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1688, hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h0, h1387, h1607, h1688, h1690, hc12, hc23, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1689, hlam, p1691_0]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [h1690, hlam, p1691_1]
                    · have p1691_0 := h1691c.1
                      have p1691_1 := h1691c.2.1
                      have p1691_2 := h1691c.2.2.1
                      have p1691_3 := h1691c.2.2.2
                      linarith only [hlam, p1691_0]
                  · rcases h2bigk with h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c | h1717c
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1387, hc12, hc24, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1387, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1549, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h0, hlam, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1681, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1683, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1685, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h0, h1387, hc12, hc23, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1717_1, u5ehi2]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1688, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1690, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1689, hlam, p1717_0]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [h1690, hc24, hc45, hlam, hphi, p1717_1]
                    · have p1717_0 := h1717c.1
                      have p1717_1 := h1717c.2.1
                      have p1717_2 := h1717c.2.2.1
                      have p1717_3 := h1717c.2.2.2
                      linarith only [hlam, p1717_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1743 | h1743
                  · linarith only [h0, h1387, h1607, h1688, h1689, h1743, hc12, hc35, hlam, hphi, ht23]
                  · rcases h2bigk with h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1387, hc12, hc24, hlam, hphi, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1, hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1387, hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1549, hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h0, hlam, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1681, hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1683, hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1685, hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1689, hc02, hc35, hlam, hphi, ht23, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1689, hc12, hc35, hlam, hphi, ht23, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1689, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1689, hlam, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1688, hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1743, hlam, p1745_0]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h1689, hc23, hc35, hlam, hphi, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [h0, h1387, h1743, hc12, hc45, hlam, hphi, ht23, ht34, p1745_1]
                    · have p1745_0 := h1745c.1
                      have p1745_1 := h1745c.2.1
                      have p1745_2 := h1745c.2.2.1
                      have p1745_3 := h1745c.2.2.2
                      linarith only [hlam, p1745_0]
              · linarith only [h1, h1606, h1688, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1772 | h1772
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1773 | h1773
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1774 | h1774
                  · linarith only [h1606, h1607, h1681, h1687, h1774, hc12, hc24, hlam, hphi]
                  · rcases h2bigk with h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1, hc12, hc23, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1387, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1549, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h0, hlam, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1681, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1683, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1685, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h0, h1387, hc12, hc23, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1776_1, u5ehi2]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1772, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1774, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1773, hlam, p1776_0]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [h1774, hc24, hc45, hlam, hphi, p1776_1]
                    · have p1776_0 := h1776c.1
                      have p1776_1 := h1776c.2.1
                      have p1776_2 := h1776c.2.2.1
                      have p1776_3 := h1776c.2.2.2
                      linarith only [hlam, p1776_0]
                · linarith only [h1, h1606, h1681, h1687, h1773, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1, h1606, h1772, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1804 | h1804
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1805 | h1805
      · linarith only [h0, h1, h1805, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1807 | h1807
        · linarith only [h0, h1387, h1807, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1809 | h1809
          · linarith only [h0, h1549, h1809, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1811 | h1811
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1812 | h1812
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1813 | h1813
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1814 | h1814
                  · rcases h2bigk with h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c | h1815c
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1, h1606, h1805, h1811, hc12, hc23, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1, hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1387, hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1549, hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h0, hlam, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1805, hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1807, hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1809, hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1606, h1807, h1811, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h0, h1549, hc12, hc23, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1812, hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h0, h1549, h1812, hc12, hc23, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1813, hlam, p1815_0]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [h1814, hlam, p1815_1]
                    · have p1815_0 := h1815c.1
                      have p1815_1 := h1815c.2.1
                      have p1815_2 := h1815c.2.2.1
                      have p1815_3 := h1815c.2.2.2
                      linarith only [hlam, p1815_0]
                  · linarith only [h0, h1387, h1606, h1804, h1814, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1606, h1804, h1805, h1811, h1813, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · linarith only [h1805, h1811, h1812, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1844 | h1844
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1845 | h1845
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1846 | h1846
                  · rcases h2bigk with h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1, hc12, hc23, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1, hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1387, hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1549, hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h0, hlam, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1805, hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1807, hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1809, hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1846, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1847_1, u5ehi2]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h0, h1549, hc12, hc23, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1844, hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h0, h1549, h1844, hc12, hc23, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1845, hlam, p1847_0]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [h1846, hlam, p1847_1]
                    · have p1847_0 := h1847c.1
                      have p1847_1 := h1847c.2.1
                      have p1847_2 := h1847c.2.2.1
                      have p1847_3 := h1847c.2.2.2
                      linarith only [hlam, p1847_0]
                  · linarith only [h1387, h1804, h1846, hlam]
                · linarith only [h1811, h1844, h1845, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1875 | h1875
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1876 | h1876
                  · rcases h2bigk with h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1, hc12, hc23, hlam, hphi, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1, hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1387, hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1549, hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h0, hlam, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1805, hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1807, hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1809, hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1844, hc12, hc34, hlam, hphi, ht23, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1844, hlam, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1877_1, u5ehi2]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1844, hc23, hc34, hlam, hphi, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h0, h1549, h1844, hc12, hc34, hlam, hphi, ht23, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1875, hlam, p1877_0]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [h1876, hlam, p1877_1]
                    · have p1877_0 := h1877c.1
                      have p1877_1 := h1877c.2.1
                      have p1877_2 := h1877c.2.2.1
                      have p1877_3 := h1877c.2.2.2
                      linarith only [hlam, p1877_0]
                  · linarith only [h1387, h1804, h1876, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1904 | h1904
                  · rcases h2bigk with h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1, h1875, hc12, hc35, hlam, hphi, ht23, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1, hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1387, hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1549, hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h0, hlam, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1805, hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1807, hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1809, hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1875, hc02, hc35, hlam, hphi, ht23, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1875, hc12, hc35, hlam, hphi, ht23, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1844, hlam, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1875, hlam, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h0, h1844, hc12, hc34, hlam, hphi, ht23, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1844, hc12, hc34, hlam, hphi, ht23, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1844, hc23, hc34, hlam, hphi, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [hlam, p1905_0]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1905_1, u5ehi2]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h0, h1, h1875, hc12, hc35, hlam, hphi, ht23, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [h1904, hlam, p1905_1]
                    · have p1905_0 := h1905c.1
                      have p1905_1 := h1905c.2.1
                      have p1905_2 := h1905c.2.2.1
                      have p1905_3 := h1905c.2.2.2
                      linarith only [hlam, p1905_0]
                  · linarith only [h1387, h1804, h1904, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1932 | h1932
      · linarith only [h0, h1, h1932, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1934 | h1934
        · linarith only [h0, h1387, h1934, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1936 | h1936
          · linarith only [h0, h1549, h1936, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1938 | h1938
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1939 | h1939
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1940 | h1940
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1941 | h1941
                  · rcases h2bigk with h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c | h1942c
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1, h1606, h1804, h1939, h1941, hc12, hc23, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1387, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1549, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h0, hlam, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1932, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1934, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1936, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1606, h1804, h1941, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h0, h1, h1606, h1804, h1941, hc12, hc23, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1939, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h0, h1, h1606, h1804, h1939, h1941, hc12, hc23, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1940, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1941, hlam, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
                  · rcases h2bigk with h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c | h1968c
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1, h1606, h1938, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1387, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1549, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h0, hlam, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1932, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1934, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1936, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1606, h1934, h1938, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1968_1, u5ehi2]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1939, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1941, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h1940, hlam, p1968_0]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [h0, h1, h1606, h1934, h1938, h1941, hc12, hc45, hlam, hphi, ht23, ht34, p1968_1]
                    · have p1968_0 := h1968c.1
                      have p1968_1 := h1968c.2.1
                      have p1968_2 := h1968c.2.2.1
                      have p1968_3 := h1968c.2.2.2
                      linarith only [hlam, p1968_0]
                · linarith only [h0, h1, h1606, h1932, h1938, h1940, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1932, h1938, h1939, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1996 | h1996
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1997 | h1997
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1998 | h1998
                  · rcases h2bigk with h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1, hc12, hc23, hlam, hphi, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1, hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1387, hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1549, hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h0, hlam, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1932, hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1934, hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1936, hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1804, h1998, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1999_1, u5ehi0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1999_1, u5ehi2]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1996, hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h0, h1549, h1996, hc12, hc23, hlam, hphi, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1997, hlam, p1999_0]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [h1998, hlam, p1999_1]
                    · have p1999_0 := h1999c.1
                      have p1999_1 := h1999c.2.1
                      have p1999_2 := h1999c.2.2.1
                      have p1999_3 := h1999c.2.2.2
                      linarith only [hlam, p1999_0]
                  · rcases h2bigk with h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1, hc12, hc23, hlam, hphi, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1387, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1549, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h0, hlam, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1932, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1934, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1936, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1938, h1996, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2025_1, u5ehi2]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1996, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1998, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1997, hlam, p2025_0]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [h1998, hc24, hc45, hlam, hphi, p2025_1]
                    · have p2025_0 := h2025c.1
                      have p2025_1 := h2025c.2.1
                      have p2025_2 := h2025c.2.2.1
                      have p2025_3 := h2025c.2.2.2
                      linarith only [hlam, p2025_0]
                · linarith only [h0, h1, h1606, h1996, h1997, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2052 | h2052
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2053 | h2053
                  · rcases h2bigk with h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1, h1606, h1804, h2053, hc12, hc24, hlam, hphi, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1, hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1387, hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1549, hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h0, hlam, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1932, hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1934, hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1936, hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1996, hc02, hc34, hlam, hphi, ht23, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1996, hc12, hc34, hlam, hphi, ht23, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1996, hlam, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2054_1, u5ehi2]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h1996, hc23, hc34, hlam, hphi, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h0, h1549, h1996, hc12, hc34, hlam, hphi, ht23, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h2052, hlam, p2054_0]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [h2053, hlam, p2054_1]
                    · have p2054_0 := h2054c.1
                      have p2054_1 := h2054c.2.1
                      have p2054_2 := h2054c.2.2.1
                      have p2054_3 := h2054c.2.2.2
                      linarith only [hlam, p2054_0]
                  · linarith only [h1996, h2052, h2053, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2081 | h2081
                  · rcases h2bigk with h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1, h1606, h1804, h2081, hc12, hc24, hlam, hphi, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1, hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1387, hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1549, hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h0, hlam, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1932, hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1934, hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1936, hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1996, hlam, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h2052, hlam, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1996, hc23, hc34, hlam, hphi, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hlam, p2082_0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h1549, h1996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2082_1, u5ehi0]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h0, hc12, hc25, hlam, hphi, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h0, h1, h2052, hc12, hc35, hlam, hphi, ht23, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [h2081, hlam, p2082_1]
                    · have p2082_0 := h2082c.1
                      have p2082_1 := h2082c.2.1
                      have p2082_2 := h2082c.2.2.1
                      have p2082_3 := h2082c.2.2.2
                      linarith only [hlam, p2082_0]
                  · rcases h2bigk with h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c | h2108c
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1, hc12, hc23, hlam, hphi, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1, hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1387, hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1549, hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h0, hlam, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1932, hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1934, hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1936, hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [hc02, hc23, hlam, hphi, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1996, hc12, hc24, hlam, hphi, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1996, hlam, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h2052, hlam, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h0, hc12, hc24, hlam, hphi, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h0, h1, hc12, hc24, hlam, hphi, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h2081, hlam, p2108_0]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h0, h2081, hc12, hc45, hlam, hphi, ht23, ht34, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h2081, hc12, hc45, hlam, hphi, ht23, ht34, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h0, h1, h2081, hc12, hc45, hlam, hphi, ht23, ht34, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [h1387, h2081, hc04, hc45, hlam, hphi, p2108_1]
                    · have p2108_0 := h2108c.1
                      have p2108_1 := h2108c.2.1
                      have p2108_2 := h2108c.2.2.1
                      have p2108_3 := h2108c.2.2.2
                      linarith only [hlam, p2108_0]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1387 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1549 | h1549
  · exact r1l7_22_15_H_I_L_R_x0_x1_x1_x0 m hb2 hb5 h0 h1 h1387 h1549
  · exact r1l7_22_15_H_I_L_R_x0_x1_x1_x1 m hb2 hb5 h0 h1 h1387 h1549

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1387 | h1387
  · exact r1l7_22_15_H_I_L_R_x0_x1_x0 m hb2 hb5 h0 h1 h1387
  · exact r1l7_22_15_H_I_L_R_x0_x1_x1 m hb2 hb5 h0 h1 h1387

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_22_15_H_I_L_R_x0_x0 m hb2 hb5 h0 h1
  · exact r1l7_22_15_H_I_L_R_x0_x1 m hb2 hb5 h0 h1

end R2N4
