import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1662 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1663 | h1663
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1664 | h1664
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1665 | h1665
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1666 | h1666
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1667 | h1667
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1668 | h1668
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1669 | h1669
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1670 | h1670
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1671 | h1671
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1672 | h1672
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1673 | h1673
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1674 | h1674
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1675 | h1675
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1676 | h1676
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1677 | h1677
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1678 | h1678
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1679 | h1679
                                  · linarith only [h0, h1662, h1671, h1676, h1679, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h1663, h1675, h1679, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h1663, h1675, h1678, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h1669, h1677, hc23, hlam, hphi, u3elo0]
                            · linarith only [h1668, h1676, hc23, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1685 | h1685
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1686 | h1686
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1687 | h1687
                                · linarith only [h1672, h1675, h1687, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1689 | h1689
                                  · linarith only [h1672, h1675, h1685, h1689, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · rcases h0bigk with h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c | h1691c
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, hlam, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, h1662, h1671, h1686, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, h1670, h1672, h1675, h1685, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, h1670, h1672, h1675, h1685, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1662, hlam, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1665, hlam, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1662, h1670, h1672, h1675, h1685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1691_1, u3elo0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1663, hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1666, hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1668, hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h0, h1663, h1664, h1673, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1664, hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1667, hlam, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1669, hlam, p1691_0]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [h1670, hlam, p1691_1]
                                    · have p1691_0 := h1691c.1
                                      have p1691_1 := h1691c.2.1
                                      have p1691_2 := h1691c.2.2.1
                                      have p1691_3 := h1691c.2.2.2
                                      linarith only [hlam, p1691_0]
                              · linarith only [h1669, h1685, h1686, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h1668, h1685, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1669, h1674, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h1667, h1673, hlam]
                    · linarith only [h0, h1666, h1672, hlam]
                  · linarith only [h0, h1671, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1723 | h1723
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1724 | h1724
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1725 | h1725
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1726 | h1726
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1727 | h1727
                          · linarith only [h0, h1663, h1670, h1727, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1729 | h1729
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1730 | h1730
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1731 | h1731
                                · linarith only [h1663, h1670, h1724, h1731, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1733 | h1733
                                  · linarith only [h1668, h1670, h1733, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                  · rcases h0bigk with h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h0, hlam, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h0, h1663, h1670, h1724, h1729, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1662, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h0, h1662, h1723, h1730, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      rcases p1735_3 (m.d 0 1) (by simp) with h1744 | h1744
                                      · linarith only [h0, h1744, hlam]
                                      · linarith only [h1663, h1744, hlam]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      rcases p1735_3 (m.d 0 1) (by simp) with h1747 | h1747
                                      · linarith only [h0, h1747, hlam]
                                      · linarith only [h1664, h1747, hlam]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1662, hlam, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1665, hlam, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1663, h1724, h1729, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1735_1, u3elo0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1663, h1670, h1724, h1729, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1735_1, u3elo0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1663, hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1666, hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1668, hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1670, hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1664, hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1667, hlam, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h1669, hlam, p1735_0]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [h0, h1663, h1664, h1724, h1729, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1735_1]
                                    · have p1735_0 := h1735c.1
                                      have p1735_1 := h1735c.2.1
                                      have p1735_2 := h1735c.2.2.1
                                      have p1735_3 := h1735c.2.2.2
                                      linarith only [hlam, p1735_0]
                              · linarith only [h1669, h1730, hc23, hlam, hphi, u3elo0]
                            · linarith only [h1668, h1729, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1669, h1726, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h1667, h1725, hlam]
                    · linarith only [h0, h1666, h1724, hlam]
                  · linarith only [h0, h1723, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1771 | h1771
                · linarith only [h1668, h1669, h1771, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1773 | h1773
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1774 | h1774
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1775 | h1775
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1776 | h1776
                        · linarith only [h1669, h1776, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1778 | h1778
                          · linarith only [h1663, h1771, h1778, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1780 | h1780
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1781 | h1781
                              · linarith only [h1662, h1669, h1773, h1781, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1783 | h1783
                                · linarith only [h0, h1662, h1663, h1669, h1771, h1773, h1774, h1780, h1783, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1785 | h1785
                                  · linarith only [h1662, h1663, h1669, h1771, h1773, h1774, h1780, h1785, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                  · rcases h0bigk with h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h0, hlam, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h0, h1663, h1774, h1780, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h0, h1662, h1669, h1773, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h0, h1668, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      rcases p1787_3 (m.d 0 1) (by simp) with h1796 | h1796
                                      · linarith only [h0, h1796, hlam]
                                      · linarith only [h1663, h1796, hlam]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h0, h1662, h1669, h1773, h1780, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1662, hlam, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1665, hlam, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1663, h1669, h1774, h1780, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1787_1, u3elo4]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1669, hlam, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1663, hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1666, hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1668, hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1771, hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1664, hlam, p1787_0]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1667, hlam, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h1662, h1773, h1780, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [h0, h1663, h1664, h1774, h1780, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1787_1]
                                    · have p1787_0 := h1787c.1
                                      have p1787_1 := h1787c.2.1
                                      have p1787_2 := h1787c.2.2.1
                                      have p1787_3 := h1787c.2.2.2
                                      linarith only [hlam, p1787_0]
                            · linarith only [h1668, h1780, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h1667, h1775, hlam]
                    · linarith only [h0, h1666, h1774, hlam]
                  · linarith only [h0, h1773, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1819 | h1819
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1820 | h1820
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1821 | h1821
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1822 | h1822
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1823 | h1823
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1824 | h1824
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1825 | h1825
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1826 | h1826
                            · linarith only [h0, h1662, h1668, h1821, h1826, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1828 | h1828
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1829 | h1829
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1830 | h1830
                                  · rcases h0bigk with h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [hlam, p1831_0]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h0, hlam, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [hlam, p1831_0]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h0, h1665, h1828, h1830, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h0, h1663, h1822, h1826, h1828, h1830, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      rcases p1831_3 (m.d 0 1) (by simp) with h1841 | h1841
                                      · linarith only [h0, h1841, hlam]
                                      · linarith only [h1664, h1841, hlam]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1662, hlam, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1665, hlam, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [hlam, p1831_0]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1668, hlam, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1668, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1831_1, u3elo3]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1663, hlam, p1831_0]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1666, hlam, p1831_0]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1662, h1821, h1828, h1830, hc04, hc45, hlam, hphi, ht0b, ht5b, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [hlam, p1831_0]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h0, h1663, h1664, h1823, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1664, hlam, p1831_0]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1667, hlam, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1819, hlam, p1831_0]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [h1820, hlam, p1831_1]
                                    · have p1831_0 := h1831c.1
                                      have p1831_1 := h1831c.2.1
                                      have p1831_2 := h1831c.2.2.1
                                      have p1831_3 := h1831c.2.2.2
                                      linarith only [hlam, p1831_0]
                                  · linarith only [h0, h1663, h1668, h1820, h1830, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h1668, h1820, h1826, h1828, h1829, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h1668, h1819, h1828, hc23, hlam, hphi, u3elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1862 | h1862
                            · linarith only [h1668, h1819, h1820, h1822, h1825, h1862, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h1668, h1819, h1820, h1822, h1825, h1862, hc23, hlam, hphi, u3elo3]
                        · linarith only [h1668, h1819, h1824, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1667, h1823, hlam]
                    · linarith only [h0, h1666, h1822, hlam]
                  · linarith only [h0, h1821, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1668, h1819, h1820, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1870 | h1870
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1871 | h1871
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1872 | h1872
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1873 | h1873
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1874 | h1874
                        · linarith only [h1819, h1874, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1876 | h1876
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1877 | h1877
                            · linarith only [h0, h1663, h1668, h1871, h1874, h1876, h1877, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1879 | h1879
                              · linarith only [h1662, h1819, h1871, h1879, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1881 | h1881
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1882 | h1882
                                  · rcases h0bigk with h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [hlam, p1883_0]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h0, hlam, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [hlam, p1883_0]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      rcases p1883_3 (m.d 0 1) (by simp) with h1891 | h1891
                                      · linarith only [h0, h1891, hlam]
                                      · linarith only [h1662, h1891, hlam]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h0, h1663, h1872, h1881, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      rcases p1883_3 (m.d 0 1) (by simp) with h1895 | h1895
                                      · linarith only [h0, h1895, hlam]
                                      · linarith only [h1664, h1895, hlam]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1662, hlam, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1665, hlam, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [hlam, p1883_0]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1668, hlam, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1819, hlam, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1663, hlam, p1883_0]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1666, hlam, p1883_0]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h0, h1662, h1663, h1871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [hlam, p1883_0]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1662, h1668, h1819, h1871, hc23, hlam, hphi, p1883_1, u3elo3]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1664, hlam, p1883_0]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1667, hlam, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h0, h1662, h1664, h1871, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [h1870, hlam, p1883_1]
                                    · have p1883_0 := h1883c.1
                                      have p1883_1 := h1883c.2.1
                                      have p1883_2 := h1883c.2.2.1
                                      have p1883_3 := h1883c.2.2.2
                                      linarith only [hlam, p1883_0]
                                  · linarith only [h0, h1663, h1668, h1872, h1881, h1882, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h1663, h1876, h1881, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1915 | h1915
                            · linarith only [h1662, h1668, h1870, h1871, h1872, h1876, h1915, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h1668, h1870, h1872, h1876, h1915, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1667, h1873, hlam]
                    · linarith only [h0, h1666, h1872, hlam]
                  · linarith only [h0, h1871, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1921 | h1921
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1922 | h1922
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1923 | h1923
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1924 | h1924
                        · linarith only [h1662, h1819, h1924, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1926 | h1926
                          · linarith only [h0, h1663, h1870, h1926, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1928 | h1928
                            · linarith only [h1662, h1668, h1921, h1928, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1930 | h1930
                              · linarith only [h1662, h1819, h1921, h1930, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1932 | h1932
                                · linarith only [h0, h1663, h1668, h1870, h1922, h1932, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1934 | h1934
                                  · linarith only [h1666, h1870, h1928, h1934, hc23, hlam, hphi, u3elo3]
                                  · rcases h0bigk with h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, h1662, h1921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, h1662, h1668, h1921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, h1662, h1668, h1870, h1921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 1) (by simp) with h1944 | h1944
                                      · linarith only [h0, h1944, hlam]
                                      · linarith only [h1662, h1944, hlam]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 1) (by simp) with h1947 | h1947
                                      · linarith only [h0, h1947, hlam]
                                      · linarith only [h1663, h1947, hlam]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 1) (by simp) with h1950 | h1950
                                      · linarith only [h0, h1950, hlam]
                                      · linarith only [h1664, h1950, hlam]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1662, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1665, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1668, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1819, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1663, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1666, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, h1662, h1663, h1921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1870, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1664, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1667, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1662, h1819, h1921, hc23, hlam, hphi, p1936_1, u3elo4]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1819, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1936_1, u3elo4]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                      · linarith only [h0, h1667, h1923, hlam]
                    · linarith only [h0, h1666, h1922, hlam]
                  · linarith only [h0, h1921, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h0, h1664, h1667, hlam]
        · linarith only [h0, h1663, h1666, hlam]
      · linarith only [h0, h1662, h1665, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1974 | h1974
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1975 | h1975
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1976 | h1976
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1977 | h1977
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1978 | h1978
              · linarith only [h1662, h1664, h1978, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1980 | h1980
                · linarith only [h1662, h1664, h1977, h1980, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1982 | h1982
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1983 | h1983
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1984 | h1984
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1985 | h1985
                        · linarith only [h1662, h1664, h1978, h1985, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1662, h1664, h1985, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1662, h1976, h1982, h1984, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1975, h1983, hlam]
                  · linarith only [h0, h1982, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1991 | h1991
              · linarith only [h1663, h1664, h1977, h1991, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1993 | h1993
                · linarith only [h1663, h1664, h1993, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1995 | h1995
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1996 | h1996
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1997 | h1997
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1998 | h1998
                        · linarith only [h1662, h1664, h1991, h1997, h1998, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1662, h1664, h1995, h1998, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h1662, h1976, h1995, h1997, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1975, h1996, hlam]
                  · linarith only [h0, h1662, h1995, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2004 | h2004
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2005 | h2005
              · linarith only [h0, h1662, h1976, h2005, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2007 | h2007
                · linarith only [h0, h1662, h1976, h2004, h2007, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2009 | h2009
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2010 | h2010
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2011 | h2011
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2012 | h2012
                        · linarith only [h0, h1662, h1976, h2005, h2011, h2012, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h1662, h1976, h2011, h2012, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2015 | h2015
                        · linarith only [h0, h1662, h2011, h2015, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1662, h2011, h2015, hc13, hlam, hphi, u3elo4]
                    · linarith only [h0, h1662, h1975, h2009, h2010, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1662, h2009, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2020 | h2020
              · linarith only [h1974, h1976, h2004, h2020, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2022 | h2022
                · linarith only [h0, h1663, h1976, h2022, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2024 | h2024
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2025 | h2025
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2026 | h2026
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2027 | h2027
                        · linarith only [h2020, h2027, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1662, h1664, h2024, h2027, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2030 | h2030
                        · linarith only [h0, h1662, h2026, h2030, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1662, h2026, h2030, hc13, hlam, hphi, u3elo4]
                    · linarith only [h0, h1662, h1975, h2024, h2025, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1662, h2024, hc13, hlam, hphi, u3elo2]
        · linarith only [h0, h1663, h1975, hlam]
      · linarith only [h0, h1662, h1974, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2037 | h2037
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2038 | h2038
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2039 | h2039
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2040 | h2040
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2041 | h2041
            · linarith only [h1662, h1663, h2041, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2043 | h2043
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2044 | h2044
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2045 | h2045
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2046 | h2046
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2047 | h2047
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2048 | h2048
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2049 | h2049
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2050 | h2050
                            · linarith only [h2041, h2050, hc03, hlam, hphi, u3elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2052 | h2052
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2053 | h2053
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2054 | h2054
                                  · rcases h0bigk with h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [hlam, p2055_0]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h0, hlam, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h1662, h2045, h2052, h2054, hc01, hc45, hlam, hphi, ht0b, ht5b, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h1663, hlam, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h1663, h2041, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2055_1, u3elo3]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [hlam, p2055_0]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h0, h1662, h2045, h2052, h2054, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h0, h1662, h1663, h2045, h2052, h2054, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      rcases p2055_3 (m.d 0 1) (by simp) with h2065 | h2065
                                      · linarith only [h0, h2065, hlam]
                                      · linarith only [h2037, h2065, hlam]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h1662, hlam, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2038, hlam, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [hlam, p2055_0]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2041, hlam, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2037, h2047, h2052, h2054, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2055_1, u3elo0]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h1662, h2045, h2052, h2054, hc04, hc45, hlam, hphi, ht0b, ht5b, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2039, hlam, p2055_0]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2041, hc03, hlam, hphi, p2055_1, u3elo3]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [hlam, p2055_0]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2037, h2041, h2047, h2052, h2054, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2055_1, u3elo3]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2037, hlam, p2055_0]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2040, hlam, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2043, hlam, p2055_0]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [h2044, hlam, p2055_1]
                                    · have p2055_0 := h2055c.1
                                      have p2055_1 := h2055c.2.1
                                      have p2055_2 := h2055c.2.2.1
                                      have p2055_3 := h2055c.2.2.2
                                      linarith only [hlam, p2055_0]
                                  · linarith only [h2041, h2044, h2054, hlam]
                                · linarith only [h0, h1662, h2048, h2049, h2050, h2052, h2053, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h2043, h2052, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1662, h1663, h2049, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h2041, h2043, h2045, h2048, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h2040, h2047, hlam]
                    · linarith only [h0, h2039, h2046, hlam]
                  · linarith only [h0, h2045, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1663, h2037, h2044, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2092 | h2092
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2093 | h2093
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2094 | h2094
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2095 | h2095
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2096 | h2096
                        · linarith only [h1662, h1663, h2043, h2094, h2096, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2098 | h2098
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2099 | h2099
                            · linarith only [h1662, h1663, h2041, h2093, h2099, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2101 | h2101
                              · linarith only [h1662, h2043, h2093, h2101, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2103 | h2103
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2104 | h2104
                                  · rcases h0bigk with h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h0, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1662, h1663, h2093, h2094, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1663, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1663, h2094, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      rcases p2105_3 (m.d 0 1) (by simp) with h2113 | h2113
                                      · linarith only [h0, h2113, hlam]
                                      · linarith only [h1662, h2113, hlam]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h0, h1663, h2037, h2095, h2101, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      rcases p2105_3 (m.d 0 1) (by simp) with h2117 | h2117
                                      · linarith only [h0, h2117, hlam]
                                      · linarith only [h2037, h2117, hlam]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1662, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2038, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2041, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2043, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2037, h2095, h2101, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2039, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1662, h2041, h2093, hc23, hlam, hphi, p2105_1, u3elo3]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1662, h2041, h2043, h2093, hc23, hlam, hphi, p2105_1, u3elo3]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2037, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2040, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h0, h1662, h2037, h2093, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2092, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                  · linarith only [h1663, h2037, h2041, h2095, h2103, h2104, hlam]
                                · linarith only [h1663, h2037, h2041, h2098, h2099, h2103, hc23, hlam, hphi, u3elo3]
                          · linarith only [h1663, h2041, h2092, h2098, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h2040, h2095, hlam]
                    · linarith only [h0, h2039, h2094, hlam]
                  · linarith only [h0, h1662, h2093, hc13, hlam, hphi, u3elo2]
                · linarith only [h1663, h2037, h2092, hlam]
          · linarith only [h0, h2037, h2040, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2143 | h2143
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2144 | h2144
            · linarith only [h0, h1662, h2039, h2144, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2146 | h2146
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2147 | h2147
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2148 | h2148
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2149 | h2149
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2150 | h2150
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2151 | h2151
                        · linarith only [h0, h1662, h2039, h2149, h2151, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2144, h2146, h2151, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1662, h2039, h2148, h2149, h2150, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2155 | h2155
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2156 | h2156
                        · linarith only [h0, h1662, h2149, h2156, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h2144, h2146, h2156, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h2037, h2039, h2143, h2155, hc04, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1662, h2148, hc13, hlam, hphi, u3elo2]
                · linarith only [h0, h2037, h2039, h2147, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2162 | h2162
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2163 | h2163
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2164 | h2164
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2165 | h2165
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2166 | h2166
                        · linarith only [h0, h1662, h2039, h2146, h2164, h2166, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2168 | h2168
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2169 | h2169
                            · linarith only [h0, h1662, h2039, h2144, h2163, h2164, h2169, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h2037, h2039, h2163, h2166, h2169, hc23, hlam, hphi, u3elo3]
                          · linarith only [h1663, h2037, h2163, h2166, h2168, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h2039, h2164, h2165, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2174 | h2174
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2175 | h2175
                        · linarith only [h0, h1662, h2146, h2164, h2175, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2177 | h2177
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2178 | h2178
                            · linarith only [h0, h1662, h2039, h2144, h2178, hc13, hlam, hphi, u3elo2]
                            · linarith only [h0, h2037, h2163, h2164, h2175, h2178, hc23, hlam, hphi, u3elo3]
                          · linarith only [h1663, h2037, h2163, h2175, h2177, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1662, h2143, h2163, h2174, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1662, h2163, hc13, hlam, hphi, u3elo2]
                · linarith only [h0, h2037, h2039, h2162, hlam]
          · linarith only [h0, h2037, h2143, hlam]
      · linarith only [h0, h1662, h2038, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2187 | h2187
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2188 | h2188
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2189 | h2189
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2190 | h2190
            · linarith only [h1662, h1663, h2190, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2192 | h2192
              · linarith only [h1662, h2037, h2192, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2194 | h2194
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2195 | h2195
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2196 | h2196
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2197 | h2197
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2198 | h2198
                        · linarith only [h1662, h1663, h2192, h2196, h2198, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1662, h2037, h2195, h2198, hc23, hlam, hphi, u3elo4]
                      · linarith only [h1662, h1663, h2189, h2195, h2196, h2197, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h2188, h2196, hlam]
                  · linarith only [h0, h2195, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2204 | h2204
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2205 | h2205
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2206 | h2206
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2207 | h2207
                        · linarith only [h1662, h1663, h2192, h2194, h2207, hlam]
                        · linarith only [h1662, h2037, h2207, hc13, hlam, hphi, u3elo4]
                      · linarith only [h1662, h1663, h2189, h2204, h2205, h2206, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h2188, h2205, hlam]
                  · linarith only [h0, h1662, h2204, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2213 | h2213
            · linarith only [h1662, h1663, h2213, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2215 | h2215
              · linarith only [h1662, h1663, h2188, h2189, h2215, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2217 | h2217
                · linarith only [h2188, h2189, h2217, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2219 | h2219
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2220 | h2220
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2221 | h2221
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2222 | h2222
                        · linarith only [h1662, h1663, h2188, h2189, h2215, h2221, h2222, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1662, h1663, h2188, h2189, h2219, h2221, h2222, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2225 | h2225
                        · linarith only [h1662, h1663, h2220, h2221, h2225, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1662, h2037, h2219, h2225, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1662, h2188, h2189, h2220, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1662, h2219, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2230 | h2230
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2231 | h2231
            · linarith only [h0, h1662, h2188, h2231, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2233 | h2233
              · linarith only [h1662, h2037, h2233, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2235 | h2235
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2236 | h2236
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2237 | h2237
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2238 | h2238
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2239 | h2239
                        · linarith only [h1662, h2037, h2188, h2230, h2233, h2237, h2239, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1662, h2037, h2236, h2239, hc23, hlam, hphi, u3elo4]
                      · linarith only [h2188, h2230, h2237, h2238, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2243 | h2243
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2244 | h2244
                        · linarith only [h1662, h2037, h2237, h2243, h2244, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1662, h2037, h2244, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1662, h2230, h2236, h2243, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h2236, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h2188, h2230, h2235, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2250 | h2250
            · linarith only [h0, h1662, h2188, h2250, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2252 | h2252
              · linarith only [h1662, h2037, h2252, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2254 | h2254
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2255 | h2255
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2256 | h2256
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2257 | h2257
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2258 | h2258
                        · linarith only [h0, h1662, h2188, h2252, h2256, h2258, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h1662, h2230, h2255, h2257, h2258, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h1662, h2188, h2255, h2256, h2257, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2262 | h2262
                      · linarith only [h0, h1662, h2230, h2255, h2256, h2262, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2264 | h2264
                        · linarith only [h0, h1662, h2256, h2264, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1662, h2255, h2262, h2264, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h2255, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2268 | h2268
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2269 | h2269
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2270 | h2270
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2271 | h2271
                        · linarith only [h0, h1662, h2188, h2269, h2271, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h1662, h2230, h2270, h2271, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1662, h2188, h2268, h2269, h2270, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2275 | h2275
                      · linarith only [h0, h1662, h2230, h2268, h2269, h2275, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2277 | h2277
                        · linarith only [h0, h1662, h2269, h2277, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1662, h2268, h2275, h2277, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h1662, h2268, hc13, hlam, hphi, u3elo2]
      · linarith only [h0, h1662, h2187, hc13, hlam, hphi, u3elo2]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1662 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2282 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2283 | h2283
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2284 | h2284
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2285 | h2285
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2286 | h2286
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2287 | h2287
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2288 | h2288
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2289 | h2289
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2290 | h2290
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2291 | h2291
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2292 | h2292
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2293 | h2293
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2294 | h2294
                        · linarith only [h1662, h2282, h2294, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h1662, h2282, h2289, h2291, h2294, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h1662, h2293, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h2286, h2292, hlam]
                  · linarith only [h0, h2285, h2291, hlam]
                · linarith only [h0, h2284, h2290, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2301 | h2301
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2302 | h2302
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2303 | h2303
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2304 | h2304
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2305 | h2305
                        · linarith only [h1662, h2282, h2289, h2305, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2307 | h2307
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2308 | h2308
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2309 | h2309
                              · linarith only [h1662, h2282, h2289, h2302, h2309, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2311 | h2311
                                · linarith only [h2282, h2289, h2302, h2307, h2311, hlam]
                                · rcases h0bigk with h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c | h2313c
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h0, hlam, p2313_1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h1662, hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h1662, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2313_1, u3elo1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h1662, h2282, h2289, h2302, h2307, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2313_1, u3elo1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2313_1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h0, h1662, h2282, h2302, h2307, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2313_1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    rcases p2313_3 (m.d 0 1) (by simp) with h2322 | h2322
                                    · linarith only [h0, h2322, hlam]
                                    · linarith only [h2282, h2322, hlam]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    rcases p2313_3 (m.d 0 1) (by simp) with h2325 | h2325
                                    · linarith only [h0, h2325, hlam]
                                    · linarith only [h2283, h2325, hlam]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h1662, h2283, h2302, h2305, h2307, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2313_1, u3elo1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h2284, hlam, p2313_1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h1662, h2282, h2302, h2307, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2313_1, u3elo1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h1662, h2282, h2289, h2302, h2307, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2313_1, u3elo1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h2282, hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h2285, hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h2287, hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h2289, hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h2283, hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h2286, hlam, p2313_1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h2288, hlam, p2313_0]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [h0, h2282, h2283, h2302, h2307, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2313_1]
                                  · have p2313_0 := h2313c.1
                                    have p2313_1 := h2313c.2.1
                                    have p2313_2 := h2313c.2.2.1
                                    have p2313_3 := h2313c.2.2.2
                                    linarith only [hlam, p2313_0]
                            · linarith only [h1662, h2288, h2308, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1662, h2287, h2307, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1662, h2304, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h2286, h2303, hlam]
                  · linarith only [h0, h2285, h2302, hlam]
                · linarith only [h0, h2301, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h1662, h2283, h2288, hlam]
          · linarith only [h1662, h2282, h2287, hlam]
        · linarith only [h0, h2283, h2286, hlam]
      · linarith only [h1662, h2282, h2284, h2285, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2353 | h2353
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2354 | h2354
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2355 | h2355
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2356 | h2356
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2357 | h2357
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2358 | h2358
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2359 | h2359
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2360 | h2360
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2361 | h2361
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2362 | h2362
                        · linarith only [h0, h2282, h2284, h2358, h2362, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h0, h2282, h2284, h2357, h2358, h2359, h2362, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h0, h2284, h2358, h2361, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h2284, h2358, h2360, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h2284, h2353, h2358, h2359, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h2282, h2357, h2358, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2369 | h2369
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2370 | h2370
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2371 | h2371
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2372 | h2372
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2373 | h2373
                        · linarith only [h2282, h2357, h2373, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2375 | h2375
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2376 | h2376
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2377 | h2377
                              · linarith only [h2282, h2357, h2370, h2377, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2379 | h2379
                                · linarith only [h2282, h2357, h2370, h2375, h2379, hlam]
                                · rcases h0bigk with h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h0, hlam, p2381_1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h1662, hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h0, h2282, h2370, h2375, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2381_1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2381_1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2381_1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2284, hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2282, h2284, h2369, h2370, h2375, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2381_1, u3elo1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2283, h2284, h2369, h2370, h2373, h2375, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2381_1, u3elo1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2283, h2284, h2369, h2370, h2373, h2375, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2381_1, u3elo1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2284, h2369, hc02, hlam, hphi, ht23, p2381_1, u3elo1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2282, h2284, h2369, h2370, h2375, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2381_1, u3elo1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2283, h2284, h2369, h2370, h2373, h2375, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2381_1, u3elo1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2282, hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2353, hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2355, hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2357, hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2283, hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2354, hlam, p2381_1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h2356, hlam, p2381_0]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [h0, h2282, h2283, h2370, h2375, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2381_1]
                                  · have p2381_0 := h2381c.1
                                    have p2381_1 := h2381c.2.1
                                    have p2381_2 := h2381c.2.2.1
                                    have p2381_3 := h2381c.2.2.2
                                    linarith only [hlam, p2381_0]
                            · linarith only [h0, h2284, h2376, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h2283, h2284, h2370, h2373, h2375, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h1662, h2372, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2284, h2354, h2369, h2371, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h2283, h2284, h2369, h2370, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h2282, h2369, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h1662, h2283, h2356, hlam]
          · linarith only [h0, h2282, h2284, h2355, hlam]
        · linarith only [h0, h2283, h2354, hlam]
      · linarith only [h0, h2282, h2353, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2417 | h2417
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2418 | h2418
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2419 | h2419
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2420 | h2420
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2421 | h2421
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2422 | h2422
              · linarith only [h2282, h2283, h2422, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2424 | h2424
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2425 | h2425
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2426 | h2426
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2427 | h2427
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2428 | h2428
                        · linarith only [h2282, h2283, h2422, h2424, h2427, h2428, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2430 | h2430
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2431 | h2431
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2432 | h2432
                              · linarith only [h2282, h2283, h2425, h2428, h2432, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2434 | h2434
                                · linarith only [h2283, h2417, h2428, h2430, h2434, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h0bigk with h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c | h2436c
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h0, hlam, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h1662, hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2282, h2283, h2425, h2430, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2283, hlam, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h0, h1662, h2282, h2425, h2430, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    rcases p2436_3 (m.d 0 1) (by simp) with h2445 | h2445
                                    · linarith only [h0, h2445, hlam]
                                    · linarith only [h2282, h2445, hlam]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h0, h2282, h2283, h2425, h2430, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2282, h2425, h2430, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2417, hlam, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h1662, h2282, h2425, h2430, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2436_1, u3elo1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h1662, h2282, h2283, h2425, h2430, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2436_1, u3elo1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2282, hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2418, hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2420, hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2422, hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2282, h2425, h2430, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2419, hlam, p2436_1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2421, hlam, p2436_0]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [h2282, h2283, h2425, h2427, h2430, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2436_1, u3elo1]
                                  · have p2436_0 := h2436c.1
                                    have p2436_1 := h2436c.2.1
                                    have p2436_2 := h2436c.2.2.1
                                    have p2436_3 := h2436c.2.2.2
                                    linarith only [hlam, p2436_0]
                            · linarith only [h1662, h2421, h2431, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1662, h2420, h2430, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1662, h2421, h2427, hlam]
                    · linarith only [h0, h2419, h2426, hlam]
                  · linarith only [h0, h2418, h2425, hlam]
                · linarith only [h0, h2424, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2470 | h2470
              · linarith only [h1662, h2282, h2421, h2470, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2472 | h2472
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2473 | h2473
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2474 | h2474
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2475 | h2475
                      · linarith only [h1662, h2421, h2475, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h1662, h2282, h2473, h2475, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h0, h2419, h2474, hlam]
                  · linarith only [h0, h2418, h2473, hlam]
                · linarith only [h0, h2417, h2472, hlam]
          · linarith only [h1662, h2282, h2420, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2482 | h2482
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2483 | h2483
            · linarith only [h2417, h2419, h2483, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2485 | h2485
              · linarith only [h1662, h2282, h2417, h2419, h2485, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2487 | h2487
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2488 | h2488
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2489 | h2489
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2490 | h2490
                      · linarith only [h1662, h2282, h2483, h2488, h2490, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h1662, h2282, h2488, h2490, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2493 | h2493
                      · linarith only [h1662, h2282, h2483, h2488, h2493, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h1662, h2282, h2488, h2493, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h0, h2282, h2418, h2419, h2488, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h2282, h2417, h2487, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
          · linarith only [h1662, h2282, h2482, hlam]
      · linarith only [h0, h2282, h2418, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2500 | h2500
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2501 | h2501
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2502 | h2502
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2503 | h2503
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2504 | h2504
              · linarith only [h2282, h2283, h2504, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2506 | h2506
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2507 | h2507
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2508 | h2508
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2509 | h2509
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2510 | h2510
                        · linarith only [h2282, h2283, h2417, h2501, h2504, h2506, h2510, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2512 | h2512
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2513 | h2513
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2514 | h2514
                              · linarith only [h2282, h2283, h2417, h2501, h2506, h2507, h2510, h2514, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2516 | h2516
                                · linarith only [h2282, h2283, h2507, h2510, h2512, h2516, hlam]
                                · rcases h0bigk with h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h0, hlam, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h1662, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2282, h2283, h2417, h2501, h2506, h2507, h2512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2283, hlam, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2417, h2506, hc01, hlam, hphi, ht12, ht23, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2417, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2282, h2417, h2506, h2507, h2512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2417, h2506, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2282, h2507, h2512, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2417, h2506, hc02, hlam, hphi, ht23, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2282, h2417, h2506, h2507, h2512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2282, h2283, h2417, h2506, h2507, h2512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2282, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2500, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2502, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2504, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2282, h2501, h2507, h2512, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2501, hlam, p2518_1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2503, hlam, p2518_0]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [h2282, h2417, h2501, h2506, h2507, h2512, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2518_1, u3elo1]
                                  · have p2518_0 := h2518c.1
                                    have p2518_1 := h2518c.2.1
                                    have p2518_2 := h2518c.2.2.1
                                    have p2518_3 := h2518c.2.2.2
                                    linarith only [hlam, p2518_0]
                            · linarith only [h2417, h2513, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2417, h2512, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2417, h2501, h2503, h2506, h2509, hlam]
                    · linarith only [h2417, h2501, h2508, hc12, hc23, hlam, hphi]
                  · linarith only [h2283, h2417, h2501, h2506, h2507, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2506, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2417, h2501, h2503, hlam]
          · linarith only [h0, h2282, h2417, h2502, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2552 | h2552
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2553 | h2553
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2554 | h2554
              · linarith only [h0, h2282, h2501, h2554, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2556 | h2556
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2557 | h2557
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2558 | h2558
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2559 | h2559
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2560 | h2560
                        · linarith only [h0, h2282, h2501, h2554, h2558, h2559, h2560, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2562 | h2562
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2563 | h2563
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2564 | h2564
                              · linarith only [h0, h2282, h2501, h2557, h2558, h2560, h2564, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2566 | h2566
                                · linarith only [h0, h2501, h2558, h2560, h2566, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                · rcases h0bigk with h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h0, hlam, p2568_1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h1662, hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h0, h2282, h2501, h2557, h2558, h2559, h2562, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2568_1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2283, hlam, p2568_1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2501, h2558, h2559, hc01, hc13, hlam, hphi, p2568_1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2417, hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2282, h2417, h2557, h2562, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2568_1, u3elo2]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2501, hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p2568_1, u3elo0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h1662, hc02, hlam, hphi, ht23, p2568_1, u3elo1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h1662, h2282, h2557, h2562, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2568_1, u3elo1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h0, h1662, h2282, h2501, h2557, h2562, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2568_1, u3elo1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2282, hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2500, hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2552, hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2554, hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2282, h2557, h2562, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2568_1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h0, h2282, h2501, h2557, h2558, h2560, h2562, hc34, hc45, hlam, hphi, p2568_1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h2553, hlam, p2568_0]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [h1662, h2282, h2553, h2557, h2562, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2568_1, u3elo1]
                                  · have p2568_0 := h2568c.1
                                    have p2568_1 := h2568c.2.1
                                    have p2568_2 := h2568c.2.2.1
                                    have p2568_3 := h2568c.2.2.2
                                    linarith only [hlam, p2568_0]
                            · linarith only [h2417, h2553, h2563, hlam]
                          · linarith only [h0, h2282, h2417, h2557, h2562, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h1662, h2282, h2557, h2559, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h0, h2282, h2417, h2556, h2557, h2558, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2417, h2556, h2557, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2282, h2556, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2600 | h2600
              · linarith only [h1662, h2282, h2553, h2600, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2602 | h2602
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2603 | h2603
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2604 | h2604
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2605 | h2605
                      · linarith only [h0, h2417, h2553, h2605, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h1662, h2282, h2603, h2605, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h0, h2282, h2417, h2602, h2603, h2604, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2417, h2602, h2603, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2282, h2602, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h0, h2282, h2417, h2552, hlam]
      · linarith only [h0, h2282, h2500, hlam]

end R2N4
