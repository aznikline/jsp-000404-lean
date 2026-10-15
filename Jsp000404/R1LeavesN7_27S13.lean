import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 5 (by decide) (by decide) with h1661 | h1661
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1662 | h1662
    · linarith only [h1662, h2, h3, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1664 | h1664
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1665 | h1665
        · linarith only [h1665, h2, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1667 | h1667
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1668 | h1668
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1669 | h1669
              · linarith only [h0, h1662, h1669, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1671 | h1671
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1672 | h1672
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1673 | h1673
                    · linarith only [h1662, h1664, h1673, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1675 | h1675
                      · linarith only [h1671, h1673, h1675, h2, h3, hlam]
                      · rcases h5bigk with h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1677_1, u1elo0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h3, hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1673, h1675, h3, hc34, hc45, hlam, hphi, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1662, hlam, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1, hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1665, hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1668, h1675, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1677_1, u1elo2]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1669, hlam, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1671, h1673, h2, h3, hc34, hc45, hlam, hphi, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1664, h1665, h1671, h1673, hc34, hc45, hlam, hphi, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1673, h1675, hc34, hc45, hlam, hphi, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1673, hlam, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1661, hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1668, hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1672, hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [hlam, p1677_0]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1675, hlam, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1, h1664, h1665, h1671, hc34, hc45, hlam, hphi, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1664, h1665, h1671, hc34, hc45, hlam, hphi, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1671, h2, h3, hc34, hc45, hlam, hphi, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [h1675, hc34, hc45, hlam, hphi, p1677_1]
                        · have p1677_0 := h1677c.1
                          have p1677_1 := h1677c.2.1
                          have p1677_2 := h1677c.2.2.1
                          have p1677_3 := h1677c.2.2.2
                          linarith only [hlam, p1677_0]
                  · linarith only [h1668, h1671, h1672, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1704 | h1704
                  · linarith only [h0, h1667, h1671, h1704, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h1661, h1704, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1707 | h1707
              · linarith only [h0, h1662, h1707, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1709 | h1709
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1710 | h1710
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1711 | h1711
                    · linarith only [h1661, h1662, h1664, h1668, h1711, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1713 | h1713
                      · linarith only [h1661, h1667, h1668, h1711, h1713, h3, hlam]
                      · rcases h5bigk with h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1664, h1665, h1709, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h3, hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1, h1667, h1668, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1715_1, u1elo0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1662, hlam, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1, hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1665, hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1668, hlam, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1707, hlam, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1, h1664, h1665, h1709, h1711, hc34, hc45, hlam, hphi, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1664, h1665, h1709, h1711, hc34, hc45, hlam, hphi, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1667, h1668, h1711, hc34, hc45, hlam, hphi, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1711, hlam, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1661, hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1661, h1664, h1665, h1709, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1710, hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [hlam, p1715_0]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1713, hlam, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1, h1664, h1665, h1709, hc34, hc45, hlam, hphi, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1664, h1665, h1709, hc34, hc45, hlam, hphi, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1709, h2, h3, hc34, hc45, hlam, hphi, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [h1667, h1668, hc34, hc45, hlam, hphi, p1715_1]
                        · have p1715_0 := h1715c.1
                          have p1715_1 := h1715c.2.1
                          have p1715_2 := h1715c.2.2.1
                          have p1715_3 := h1715c.2.2.2
                          linarith only [hlam, p1715_0]
                  · linarith only [h1661, h1710, h3, hlam]
                · linarith only [h1667, h1668, h1709, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1743 | h1743
            · linarith only [h1664, h1665, h1667, h1743, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1745 | h1745
              · linarith only [h0, h1662, h1745, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1747 | h1747
                · linarith only [h1, h1664, h1665, h1667, h1747, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1749 | h1749
                  · linarith only [h1664, h1665, h1743, h1747, h1749, hlam]
                  · linarith only [h1661, h1749, h3, hlam]
      · linarith only [h1664, h2, h3, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1753 | h1753
    · linarith only [h1753, h2, h3, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1755 | h1755
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1756 | h1756
        · linarith only [h1756, h2, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1758 | h1758
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1759 | h1759
            · linarith only [h1, h1661, h1759, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1761 | h1761
              · linarith only [h0, h1753, h1761, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1763 | h1763
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1764 | h1764
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1765 | h1765
                    · linarith only [h1753, h1755, h1765, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1767 | h1767
                      · linarith only [h1, h1755, h1756, h1763, h1765, h1767, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases h5bigk with h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [hlam, p1769_0]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1755, h1756, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h3, hlam, p1769_0]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1661, hlam, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1753, hlam, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1, hlam, p1769_0]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [hlam, p1769_0]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1756, hlam, p1769_0]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1759, hlam, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1761, hlam, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1, h1756, hc12, hc25, hlam, hphi, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1755, h1756, h1763, h1765, hc34, hc45, hlam, hphi, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [hlam, p1769_0]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1661, h1765, hc03, hc45, hlam, hphi, ht34, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1765, hlam, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1, h1755, h1756, h1763, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1755, h1756, h1763, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1764, hlam, p1769_0]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [hlam, p1769_0]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1767, hlam, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1, h1755, h1756, h1763, hc34, hc45, hlam, hphi, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1755, h1756, h1763, hc34, hc45, hlam, hphi, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h3, hc02, hc45, hlam, hphi, ht23, ht34, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [h1661, hc03, hc45, hlam, hphi, ht34, p1769_1]
                        · have p1769_0 := h1769c.1
                          have p1769_1 := h1769c.2.1
                          have p1769_2 := h1769c.2.2.1
                          have p1769_3 := h1769c.2.2.2
                          linarith only [hlam, p1769_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1795 | h1795
                    · linarith only [h1, h1755, h1756, h1795, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1797 | h1797
                      · linarith only [h1763, h1795, h1797, h2, h3, hlam]
                      · rcases h5bigk with h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [hlam, p1799_0]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1755, h1756, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h3, hlam, p1799_0]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1661, hlam, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1753, hlam, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1, hlam, p1799_0]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [hlam, p1799_0]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1756, hlam, p1799_0]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1759, hlam, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1761, hlam, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1, h1756, hc12, hc25, hlam, hphi, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1755, h1756, h1763, h1764, h1797, hc34, hc45, hlam, hphi, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [hlam, p1799_0]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1764, hlam, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1795, hlam, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1, h1755, h1756, h1763, h1797, hc34, hc45, hlam, hphi, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1755, h1756, h1763, h1797, hc34, hc45, hlam, hphi, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1797, h3, hc02, hc45, hlam, hphi, ht23, ht34, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [hlam, p1799_0]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1797, hlam, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1, h1755, h1756, h1763, hc34, hc45, hlam, hphi, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1755, h1756, h1763, hc34, hc45, hlam, hphi, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1763, h2, h3, hc34, hc45, hlam, hphi, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [h1764, hc23, hc45, hlam, hphi, ht34, p1799_1]
                        · have p1799_0 := h1799c.1
                          have p1799_1 := h1799c.2.1
                          have p1799_2 := h1799c.2.2.1
                          have p1799_3 := h1799c.2.2.2
                          linarith only [hlam, p1799_0]
                · linarith only [h1, h1758, h1759, h1763, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1826 | h1826
            · linarith only [h1661, h1758, h1826, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1828 | h1828
              · linarith only [h0, h1753, h1828, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1830 | h1830
                · linarith only [h1, h1755, h1756, h1758, h1830, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1832 | h1832
                  · linarith only [h1, h1661, h1755, h1756, h1830, h1832, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1834 | h1834
                    · linarith only [h1753, h1834, h2, h3, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1836 | h1836
                      · linarith only [h1830, h1834, h1836, h2, h3, hc23, hc34, hlam, hphi]
                      · rcases h5bigk with h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [hlam, p1838_0]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1755, h1756, h1830, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h3, hlam, p1838_0]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1661, hlam, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1753, hlam, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1, hlam, p1838_0]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [hlam, p1838_0]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1756, hlam, p1838_0]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1826, hlam, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1828, hlam, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1, h1755, h1756, h1830, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1755, h1756, h1830, h1832, h1836, hc23, hc45, hlam, hphi, ht34, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [hlam, p1838_0]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1832, hlam, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1834, hlam, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1, h1755, h1756, h1830, h1836, hc23, hc45, hlam, hphi, ht34, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1755, h1756, h1830, h1836, hc23, hc45, hlam, hphi, ht34, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1836, h3, hc02, hc45, hlam, hphi, ht23, ht34, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [hlam, p1838_0]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1836, hlam, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1, h1755, h1756, h1830, hc23, hc45, hlam, hphi, ht34, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1755, h1756, h1830, hc23, hc45, hlam, hphi, ht34, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1830, h2, h3, hc23, hc45, hlam, hphi, ht34, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [h1661, hc03, hc45, hlam, hphi, ht34, p1838_1]
                        · have p1838_0 := h1838c.1
                          have p1838_1 := h1838c.2.1
                          have p1838_2 := h1838c.2.2.1
                          have p1838_3 := h1838c.2.2.2
                          linarith only [hlam, p1838_0]
      · linarith only [h1755, h2, h3, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_25_L_0_H_I_s1_x0_x0 m hb1 hb5 hg0 hg1 h2 h3
  · exact r1l7_11_25_L_0_H_I_s1_x0_x1 m hb1 hb5 hg0 hg1 h2 h3

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1865 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 5 (by decide) (by decide) with h1866 | h1866
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1867 | h1867
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1868 | h1868
      · linarith only [h1865, h1868, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1870 | h1870
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1871 | h1871
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1872 | h1872
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1873 | h1873
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1874 | h1874
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1875 | h1875
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1876 | h1876
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1877 | h1877
                      · rcases h5bigk with h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1865, h1874, h2, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1878_1]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1865, h1874, h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1878_1]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1865, h1874, h1877, h2, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1878_1]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1865, h1874, h2, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1878_1]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1, hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1875, h1877, hc45, hlam, hphi, ht01, ht0b, ht5b, p1878_1, u1elo4]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h0, h1868, h1870, h1877, hc45, hlam, hphi, ht01, ht0b, ht5b, p1878_1, u1elo0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h0, h1868, h1870, hc45, hlam, hphi, ht01, ht0b, ht5b, p1878_1, u1elo0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1865, hlam, p1878_1]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1870, hlam, p1878_1]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1865, h1874, h1877, h2, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1878_1]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h0, h1868, h1870, hc45, hlam, hphi, ht01, ht0b, ht5b, p1878_1, u1elo0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1866, hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1872, hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1875, hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1866, hc03, hc45, hlam, hphi, ht0b, ht5b, p1878_1]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1867, hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1873, hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1876, hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [h1877, hlam, p1878_0]
                        · have p1878_0 := h1878c.1
                          have p1878_1 := h1878c.2.1
                          have p1878_2 := h1878c.2.2.1
                          have p1878_3 := h1878c.2.2.2
                          linarith only [hlam, p1878_0]
                      · linarith only [h0, h1873, h1877, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h0, h1873, h1876, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1865, h1866, h1874, h1875, h2, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h1865, h1871, h1874, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · linarith only [h0, h1867, h1868, h1870, h1873, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h1868, h1870, h1871, h1872, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1910 | h1910
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1911 | h1911
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1912 | h1912
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1913 | h1913
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1914 | h1914
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1915 | h1915
                      · rcases h5bigk with h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h0, h1865, h1913, h1915, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h0, h1865, h1915, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h0, h1865, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1, hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1913, h1915, hc45, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo4]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h0, h1868, h1870, h1915, hc45, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h0, h1868, h1870, hc45, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1865, hlam, p1916_1]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1870, hlam, p1916_1]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h0, h1865, h1915, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h0, h1868, h1870, hc45, hlam, hphi, ht01, ht0b, ht5b, p1916_1, u1elo0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1866, hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1910, hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1913, hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1866, hc03, hc45, hlam, hphi, ht0b, ht5b, p1916_1]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1867, hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1911, hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1914, hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [h1915, hlam, p1916_0]
                        · have p1916_0 := h1916c.1
                          have p1916_1 := h1916c.2.1
                          have p1916_2 := h1916c.2.2.1
                          have p1916_3 := h1916c.2.2.2
                          linarith only [hlam, p1916_0]
                      · linarith only [h0, h1867, h1871, h1915, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h0, h1911, h1914, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1871, h1910, h1913, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1945 | h1945
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1946 | h1946
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1947 | h1947
                      · rcases h5bigk with h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c | h1948c
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1865, h1912, h2, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1948_1]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1865, h1912, h2, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1948_1]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1865, h1912, h1947, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1948_1]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1865, h1912, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1948_1]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1, hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1945, h1947, hc45, hlam, hphi, ht01, ht0b, ht5b, p1948_1, u1elo4]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h0, h1868, h1870, h1947, hc45, hlam, hphi, ht01, ht0b, ht5b, p1948_1, u1elo0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h0, h1868, h1870, hc45, hlam, hphi, ht01, ht0b, ht5b, p1948_1, u1elo0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1865, hlam, p1948_1]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1870, hlam, p1948_1]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1865, h1912, h1947, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1948_1]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h0, h1868, h1870, hc45, hlam, hphi, ht01, ht0b, ht5b, p1948_1, u1elo0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1866, hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1910, hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1945, hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1945, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1948_1]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1867, hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1911, hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1946, hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [h1947, hlam, p1948_0]
                        · have p1948_0 := h1948c.1
                          have p1948_1 := h1948c.2.1
                          have p1948_2 := h1948c.2.2.1
                          have p1948_3 := h1948c.2.2.2
                          linarith only [hlam, p1948_0]
                      · linarith only [h1867, h1912, h1947, h2, hlam]
                    · linarith only [h0, h1911, h1946, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1871, h1910, h1945, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1867, h1871, h1910, h1911, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1978 | h1978
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1979 | h1979
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1980 | h1980
                  · linarith only [h0, h1868, h1870, h1910, h1980, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1865, h1866, h1979, h1980, h2, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1983 | h1983
                  · linarith only [h1910, h1979, h1983, hc13, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1985 | h1985
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1986 | h1986
                      · rcases h5bigk with h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1865, h1870, h1983, h2, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1987_1]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h0, h1865, h1983, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1987_1, u1elo0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h0, h1865, h1910, h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1987_1, u1elo0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h0, h1865, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1987_1, u1elo0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1, hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1983, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1987_1, u1elo4]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1910, hlam, p1987_1]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p1987_1, u1elo4]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1865, hlam, p1987_1]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1870, hlam, p1987_1]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1983, hlam, p1987_1]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1865, h1979, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1987_1]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1866, hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1866, hc03, hc15, hlam, hphi, ht0b, ht5b, p1987_1]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1865, h1866, h1979, h2, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1987_1]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h0, h1865, h1866, h1868, h1870, h1979, h1983, h2, hc23, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p1987_1, u1elo0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1867, hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1978, hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1985, hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [h1986, hlam, p1987_0]
                        · have p1987_0 := h1987c.1
                          have p1987_1 := h1987c.2.1
                          have p1987_2 := h1987c.2.2.1
                          have p1987_3 := h1987c.2.2.2
                          linarith only [hlam, p1987_0]
                      · linarith only [h1865, h1979, h1983, h1986, h2, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1865, h1978, h1985, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
              · linarith only [h0, h1867, h1868, h1870, h1978, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · linarith only [h1865, h1870, h2, hc12, hc24, hlam, hphi]
    · linarith only [h1865, h1867, h2, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2018 | h2018
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2019 | h2019
      · linarith only [h1865, h2, h2019, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2021 | h2021
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2022 | h2022
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2023 | h2023
            · linarith only [h1, h1866, h2023, hlam]
            · linarith only [h2019, h2021, h2022, h2023, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2026 | h2026
            · linarith only [h1866, h2022, h2026, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2028 | h2028
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2029 | h2029
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2030 | h2030
                  · linarith only [h1865, h1866, h2030, hlam]
                  · linarith only [h2022, h2029, h2030, hc13, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2033 | h2033
                  · linarith only [h1866, h2029, h2033, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2035 | h2035
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2036 | h2036
                      · rcases h5bigk with h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c | h2037c
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h1865, h2, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h0, h1865, h2, h2033, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2037_1, u1elo0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h1866, hlam, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h0, h1865, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p2037_1, u1elo0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h1, hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2033, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2037_1, u1elo4]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2026, hlam, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h0, h2019, h2021, hc45, hlam, hphi, ht01, ht0b, ht5b, p2037_1, u1elo0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h1865, hlam, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2021, hlam, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2033, hlam, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h1865, h2, h2029, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h1866, hc03, hc35, hlam, hphi, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2026, hc13, hc35, hlam, hphi, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2033, hc23, hc35, hlam, hphi, p2037_1]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          rcases p2037_3 (m.d 0 5) (by simp) with h2057 | h2057
                          · linarith only [h1866, h2057, hlam]
                          · linarith only [h2018, h2057, hlam]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2018, hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2028, hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2035, hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [h2036, hlam, p2037_0]
                        · have p2037_0 := h2037c.1
                          have p2037_1 := h2037c.2.1
                          have p2037_2 := h2037c.2.2.1
                          have p2037_3 := h2037c.2.2.2
                          linarith only [hlam, p2037_0]
                      · linarith only [h1865, h2, h2029, h2033, h2036, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1, h2, h2028, h2035, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h2018, h2019, h2021, h2028, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · linarith only [h1865, h2, h2021, hc12, hc24, hlam, hphi]
    · linarith only [h1865, h2, h2018, hlam]

end R2N4
