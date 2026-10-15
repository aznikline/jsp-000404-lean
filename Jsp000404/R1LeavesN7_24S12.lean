import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1160 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1498 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1640 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h1641 | h1641
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1642 | h1642
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1643 | h1643
      · linarith only [h0, h1643, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1645 | h1645
        · linarith only [h0, h1160, h1645, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1647 | h1647
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1648 | h1648
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1649 | h1649
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1650 | h1650
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1651 | h1651
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1652 | h1652
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1653 | h1653
                      · linarith only [h1, h1647, h1653, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h1649, h1653, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h1160, h1647, h1649, h1652, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h1648, h1651, h4, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1647, h1650, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1659 | h1659
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1660 | h1660
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1661 | h1661
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1662 | h1662
                      · linarith only [h1647, h1649, h1662, hlam]
                      · rcases h0bigk with h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          rcases p1664_3 (m.d 0 1) (by simp) with h1666 | h1666
                          · rcases p1664_3 (m.d 0 2) (by simp) with h1667 | h1667
                            · linarith only [h0, h1667, hlam]
                            · rcases p1664_3 (m.d 0 3) (by simp) with h1669 | h1669
                              · linarith only [h1, h1669, hlam]
                              · linarith only [h1669, h4, hlam]
                          · linarith only [h0, h1666, hlam]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1640, h1642, h1645, h1649, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1664_1, u1elo0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1642, h1645, h1649, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1664_1, u1elo0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1642, h1645, h1649, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1664_1, u1elo0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h0, hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h4, hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1160, hlam, p1664_1]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1498, hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1, hlam, p1664_1]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          rcases p1664_3 (m.d 0 1) (by simp) with h1682 | h1682
                          · rcases p1664_3 (m.d 0 2) (by simp) with h1683 | h1683
                            · linarith only [h1683, h4, hlam]
                            · rcases p1664_3 (m.d 0 3) (by simp) with h1685 | h1685
                              · rcases p1664_3 (m.d 0 4) (by simp) with h1686 | h1686
                                · linarith only [h1640, h1686, hlam]
                                · linarith only [h1160, h1686, hlam]
                              · linarith only [h1685, h4, hlam]
                          · linarith only [h0, h1682, hlam]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1642, h1645, h1649, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1664_1, u0elo2]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1, h1642, h1645, h1649, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1664_1, u1elo0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h2, hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          rcases p1664_3 (m.d 0 1) (by simp) with h1695 | h1695
                          · rcases p1664_3 (m.d 0 2) (by simp) with h1696 | h1696
                            · linarith only [h1160, h1696, hlam]
                            · rcases p1664_3 (m.d 0 3) (by simp) with h1698 | h1698
                              · rcases p1664_3 (m.d 0 4) (by simp) with h1699 | h1699
                                · rcases p1664_3 (m.d 0 5) (by simp) with h1700 | h1700
                                  · linarith only [h1642, h1700, hlam]
                                  · linarith only [h1498, h1700, hlam]
                                · linarith only [h1160, h1699, hlam]
                              · linarith only [h1698, h4, hlam]
                          · linarith only [h0, h1695, hlam]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1640, hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1642, h1645, h1649, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1664_1, u0elo3]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h3, hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          rcases p1664_3 (m.d 0 1) (by simp) with h1710 | h1710
                          · rcases p1664_3 (m.d 0 2) (by simp) with h1711 | h1711
                            · linarith only [h1498, h1711, hlam]
                            · rcases p1664_3 (m.d 0 3) (by simp) with h1713 | h1713
                              · rcases p1664_3 (m.d 0 4) (by simp) with h1714 | h1714
                                · rcases p1664_3 (m.d 0 5) (by simp) with h1715 | h1715
                                  · rcases h3bigk with h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1, h1647, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1716_1, u1elo0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h4, hlam, p1716_1]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      rcases p1716_3 (m.d 0 3) (by simp) with h1720 | h1720
                                      · rcases p1716_3 (m.d 1 3) (by simp) with h1721 | h1721
                                        · linarith only [h1, h1721, hlam]
                                        · linarith only [h1647, h1721, hlam]
                                      · linarith only [h1720, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      rcases p1716_3 (m.d 0 3) (by simp) with h1725 | h1725
                                      · rcases p1716_3 (m.d 1 3) (by simp) with h1726 | h1726
                                        · linarith only [h1, h1726, hlam]
                                        · linarith only [h1648, h1726, hlam]
                                      · linarith only [h1725, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1643, hlam, p1716_1]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1716_1, u1elo0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1, h1662, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1716_1, u1elo0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h0, h1641, hc12, hc23, hlam, hphi, p1664_1, p1716_1]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      rcases p1716_3 (m.d 0 3) (by simp) with h1736 | h1736
                                      · linarith only [h1736, h4, hlam]
                                      · linarith only [h1, h1736, hlam]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      rcases p1716_3 (m.d 0 3) (by simp) with h1740 | h1740
                                      · linarith only [h1740, h4, hlam]
                                      · linarith only [h1640, h1740, hlam]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      rcases p1716_3 (m.d 0 3) (by simp) with h1743 | h1743
                                      · linarith only [h1743, h4, hlam]
                                      · linarith only [h1641, h1743, hlam]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1640, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1647, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1659, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1662, hlam, p1716_1]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1641, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1648, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1660, hlam, p1716_0]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [h1648, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1716_1, u1elo2]
                                    · have p1716_0 := h1716c.1
                                      have p1716_1 := h1716c.2.1
                                      have p1716_2 := h1716c.2.2.1
                                      have p1716_3 := h1716c.2.2.2
                                      linarith only [hlam, p1716_0]
                                  · linarith only [h1498, h1715, hlam]
                                · linarith only [h1160, h1714, hlam]
                              · linarith only [h1713, h4, hlam]
                          · linarith only [h0, h1710, hlam]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1641, hlam, p1664_0]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [h1642, hlam, p1664_1]
                        · have p1664_0 := h1664c.1
                          have p1664_1 := h1664c.2.1
                          have p1664_2 := h1664c.2.2.1
                          have p1664_3 := h1664c.2.2.2
                          linarith only [hlam, p1664_0]
                    · linarith only [h1160, h1642, h1661, hlam]
                  · linarith only [h1, h1648, h1660, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1640, h1642, h1645, h1649, h1659, h4, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1641, h1647, h1648, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1767 | h1767
            · linarith only [h1, h1640, h1647, h1767, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1769 | h1769
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1770 | h1770
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1771 | h1771
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1772 | h1772
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1773 | h1773
                      · rcases h0bigk with h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          rcases p1774_3 (m.d 0 1) (by simp) with h1776 | h1776
                          · rcases p1774_3 (m.d 0 2) (by simp) with h1777 | h1777
                            · linarith only [h0, h1777, hlam]
                            · rcases p1774_3 (m.d 0 3) (by simp) with h1779 | h1779
                              · linarith only [h1, h1779, hlam]
                              · linarith only [h1779, h4, hlam]
                          · linarith only [h0, h1776, hlam]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1640, h1767, h1773, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1774_1, u1elo0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1769, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1774_1, u1elo0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1641, h1767, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1774_1, u1elo0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h0, hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h4, hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1160, hlam, p1774_1]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1498, hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1, hlam, p1774_1]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          rcases p1774_3 (m.d 0 1) (by simp) with h1792 | h1792
                          · rcases p1774_3 (m.d 0 2) (by simp) with h1793 | h1793
                            · linarith only [h1793, h4, hlam]
                            · rcases p1774_3 (m.d 0 3) (by simp) with h1795 | h1795
                              · rcases p1774_3 (m.d 0 4) (by simp) with h1796 | h1796
                                · linarith only [h1640, h1796, hlam]
                                · linarith only [h1160, h1796, hlam]
                              · linarith only [h1795, h4, hlam]
                          · linarith only [h0, h1792, hlam]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1640, h1643, h1767, h1773, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1774_1, u0elo2]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1, h1641, h1643, h1767, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1774_1, u1elo0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h2, hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          rcases p1774_3 (m.d 0 1) (by simp) with h1805 | h1805
                          · rcases p1774_3 (m.d 0 2) (by simp) with h1806 | h1806
                            · linarith only [h1160, h1806, hlam]
                            · rcases p1774_3 (m.d 0 3) (by simp) with h1808 | h1808
                              · rcases p1774_3 (m.d 0 4) (by simp) with h1809 | h1809
                                · rcases p1774_3 (m.d 0 5) (by simp) with h1810 | h1810
                                  · linarith only [h1642, h1810, hlam]
                                  · linarith only [h1498, h1810, hlam]
                                · linarith only [h1160, h1809, hlam]
                              · linarith only [h1808, h4, hlam]
                          · linarith only [h0, h1805, hlam]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1640, hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1641, h1643, h1767, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1774_1, u0elo3]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h3, hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          rcases p1774_3 (m.d 0 1) (by simp) with h1820 | h1820
                          · rcases p1774_3 (m.d 0 2) (by simp) with h1821 | h1821
                            · linarith only [h1498, h1821, hlam]
                            · rcases p1774_3 (m.d 0 3) (by simp) with h1823 | h1823
                              · rcases p1774_3 (m.d 0 4) (by simp) with h1824 | h1824
                                · rcases p1774_3 (m.d 0 5) (by simp) with h1825 | h1825
                                  · rcases h3bigk with h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      rcases p1826_3 (m.d 0 3) (by simp) with h1828 | h1828
                                      · rcases p1826_3 (m.d 1 3) (by simp) with h1829 | h1829
                                        · linarith only [h1, h1829, hlam]
                                        · rcases p1826_3 (m.d 2 3) (by simp) with h1831 | h1831
                                          · rcases p1826_3 (m.d 3 4) (by simp) with h1832 | h1832
                                            · linarith only [h1640, h1832, hlam]
                                            · linarith only [h1647, h1832, hlam]
                                          · linarith only [h1643, h1831, hlam]
                                      · linarith only [h1, h1828, hlam]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h4, hlam, p1826_1]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1, h1643, h1767, h1773, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1826_1, u1elo0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1, h1643, h1767, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1826_1, u1elo0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1, hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1643, hlam, p1826_1]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1647, hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1767, hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1640, h1643, h1767, h1773, hc12, hc23, hlam, hphi, p1826_1]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      rcases p1826_3 (m.d 0 3) (by simp) with h1846 | h1846
                                      · linarith only [h1846, h4, hlam]
                                      · linarith only [h1, h1846, hlam]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1643, h1767, h1773, hc12, hc23, hlam, hphi, p1826_1]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1643, h1767, hc12, hc23, hlam, hphi, p1826_1]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1640, hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1640, h1643, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1826_1, u0elo2]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1770, hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1, h1640, h1643, h1767, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1826_1, u1elo0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1641, hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1, h1641, h1643, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1826_1, u1elo0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1771, hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [h1773, hlam, p1826_0]
                                    · have p1826_0 := h1826c.1
                                      have p1826_1 := h1826c.2.1
                                      have p1826_2 := h1826c.2.2.1
                                      have p1826_3 := h1826c.2.2.2
                                      linarith only [hlam, p1826_0]
                                  · linarith only [h1498, h1825, hlam]
                                · linarith only [h1160, h1824, hlam]
                              · linarith only [h1823, h4, hlam]
                          · linarith only [h0, h1820, hlam]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1641, hlam, p1774_0]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [h1642, hlam, p1774_1]
                        · have p1774_0 := h1774c.1
                          have p1774_1 := h1774c.2.1
                          have p1774_2 := h1774c.2.2.1
                          have p1774_3 := h1774c.2.2.2
                          linarith only [hlam, p1774_0]
                      · linarith only [h1769, h1773, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1160, h1642, h1769, h1772, h3, hlam]
                  · linarith only [h0, h1, h1641, h1771, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1640, h1770, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1873 | h1873
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1874 | h1874
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1875 | h1875
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1876 | h1876
                      · linarith only [h1, h1640, h1643, h1647, h1769, h1876, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1642, h1643, h1647, h1876, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1160, h1642, h1875, hlam]
                  · linarith only [h1641, h1874, h4, hlam]
                · linarith only [h1640, h1873, h4, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1882 | h1882
      · linarith only [h0, h1641, h1882, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1884 | h1884
        · linarith only [h0, h1160, h1884, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1886 | h1886
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1887 | h1887
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1888 | h1888
              · linarith only [h1642, h1888, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1890 | h1890
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1891 | h1891
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1892 | h1892
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1893 | h1893
                      · linarith only [h1, h1160, h1642, h1886, h1893, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c | h1895c
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          rcases p1895_3 (m.d 0 1) (by simp) with h1897 | h1897
                          · rcases p1895_3 (m.d 0 2) (by simp) with h1898 | h1898
                            · linarith only [h0, h1898, hlam]
                            · rcases p1895_3 (m.d 0 3) (by simp) with h1900 | h1900
                              · linarith only [h1, h1900, hlam]
                              · linarith only [h1900, h4, hlam]
                          · linarith only [h0, h1897, hlam]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h1640, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1895_1, u1elo0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          rcases p1895_3 (m.d 0 1) (by simp) with h1905 | h1905
                          · rcases p1895_3 (m.d 0 2) (by simp) with h1906 | h1906
                            · linarith only [h0, h1906, hlam]
                            · rcases p1895_3 (m.d 0 3) (by simp) with h1908 | h1908
                              · linarith only [h1, h1908, hlam]
                              · linarith only [h1640, h1908, hlam]
                          · linarith only [h1905, h2, hlam]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          rcases p1895_3 (m.d 0 1) (by simp) with h1912 | h1912
                          · rcases p1895_3 (m.d 0 2) (by simp) with h1913 | h1913
                            · linarith only [h0, h1913, hlam]
                            · rcases p1895_3 (m.d 0 3) (by simp) with h1915 | h1915
                              · linarith only [h1, h1915, hlam]
                              · linarith only [h1641, h1915, hlam]
                          · linarith only [h1912, h3, hlam]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h0, hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h4, hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h1160, hlam, p1895_1]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h1498, hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h1, hlam, p1895_1]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          rcases p1895_3 (m.d 0 1) (by simp) with h1925 | h1925
                          · rcases p1895_3 (m.d 0 2) (by simp) with h1926 | h1926
                            · linarith only [h1926, h4, hlam]
                            · rcases p1895_3 (m.d 0 3) (by simp) with h1928 | h1928
                              · rcases p1895_3 (m.d 0 4) (by simp) with h1929 | h1929
                                · linarith only [h1640, h1929, hlam]
                                · linarith only [h1160, h1929, hlam]
                              · linarith only [h1928, h4, hlam]
                          · linarith only [h0, h1925, hlam]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          rcases p1895_3 (m.d 0 1) (by simp) with h1935 | h1935
                          · rcases p1895_3 (m.d 0 2) (by simp) with h1936 | h1936
                            · linarith only [h1936, h4, hlam]
                            · rcases p1895_3 (m.d 0 3) (by simp) with h1938 | h1938
                              · rcases p1895_3 (m.d 0 4) (by simp) with h1939 | h1939
                                · linarith only [h1640, h1939, hlam]
                                · rcases p1895_3 (m.d 0 5) (by simp) with h1941 | h1941
                                  · linarith only [h1641, h1941, hlam]
                                  · linarith only [h1642, h1941, hlam]
                              · linarith only [h1640, h1938, hlam]
                          · linarith only [h1935, h2, hlam]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          rcases p1895_3 (m.d 0 1) (by simp) with h1946 | h1946
                          · rcases p1895_3 (m.d 0 2) (by simp) with h1947 | h1947
                            · linarith only [h1947, h4, hlam]
                            · rcases p1895_3 (m.d 0 3) (by simp) with h1949 | h1949
                              · rcases p1895_3 (m.d 0 4) (by simp) with h1950 | h1950
                                · linarith only [h1640, h1950, hlam]
                                · rcases p1895_3 (m.d 0 5) (by simp) with h1952 | h1952
                                  · linarith only [h1641, h1952, hlam]
                                  · rcases h3bigk with h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1887, h1893, hc34, hlam, hphi, ht0b, ht45, ht5b, p1954_1, u0elo2]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h4, hlam, p1954_1]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      rcases p1954_3 (m.d 0 3) (by simp) with h1958 | h1958
                                      · rcases p1954_3 (m.d 1 3) (by simp) with h1959 | h1959
                                        · linarith only [h1, h1959, hlam]
                                        · linarith only [h1886, h1959, hlam]
                                      · linarith only [h1958, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      rcases p1954_3 (m.d 0 3) (by simp) with h1963 | h1963
                                      · rcases p1954_3 (m.d 1 3) (by simp) with h1964 | h1964
                                        · linarith only [h1, h1964, hlam]
                                        · linarith only [h1887, h1964, hlam]
                                      · linarith only [h1963, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1882, hlam, p1954_1]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1954_1, u1elo0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1, h1893, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1954_1, u1elo0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h0, h1160, h1642, hc12, hc23, hlam, hphi, p1895_1, p1954_1]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      rcases p1954_3 (m.d 0 3) (by simp) with h1974 | h1974
                                      · linarith only [h1974, h4, hlam]
                                      · linarith only [h1, h1974, hlam]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      rcases p1954_3 (m.d 0 3) (by simp) with h1978 | h1978
                                      · linarith only [h1978, h4, hlam]
                                      · linarith only [h1640, h1978, hlam]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      rcases p1954_3 (m.d 0 3) (by simp) with h1981 | h1981
                                      · linarith only [h1981, h4, hlam]
                                      · linarith only [h1641, h1981, hlam]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1640, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1886, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1890, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1893, hlam, p1954_1]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1641, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1887, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1891, hlam, p1954_0]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [h1887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1954_1, u1elo2]
                                    · have p1954_0 := h1954c.1
                                      have p1954_1 := h1954c.2.1
                                      have p1954_2 := h1954c.2.2.1
                                      have p1954_3 := h1954c.2.2.2
                                      linarith only [hlam, p1954_0]
                              · linarith only [h1641, h1949, hlam]
                          · linarith only [h1946, h3, hlam]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h2, hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h0, h1642, h1892, hc12, hc24, hlam, hphi, p1895_1]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h1640, hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h1642, hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h3, hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h0, h1642, h1892, hc12, hc24, hlam, hphi, p1895_1]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h1641, hlam, p1895_0]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [h0, h1160, h1642, h1892, hc12, hc24, hlam, hphi, p1895_1]
                        · have p1895_0 := h1895c.1
                          have p1895_1 := h1895c.2.1
                          have p1895_2 := h1895c.2.2.1
                          have p1895_3 := h1895c.2.2.2
                          linarith only [hlam, p1895_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2006 | h2006
                      · linarith only [h0, h1160, h1892, h2006, hc12, hc34, hlam, hphi, ht23]
                      · rcases h0bigk with h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c | h2008c
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          rcases p2008_3 (m.d 0 1) (by simp) with h2010 | h2010
                          · rcases p2008_3 (m.d 0 2) (by simp) with h2011 | h2011
                            · linarith only [h0, h2011, hlam]
                            · rcases p2008_3 (m.d 0 3) (by simp) with h2013 | h2013
                              · linarith only [h1, h2013, hlam]
                              · linarith only [h2013, h4, hlam]
                          · linarith only [h0, h2010, hlam]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h1, h1887, hc35, hlam, hphi, ht01, ht0b, ht5b, p2008_1, u1elo0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          rcases p2008_3 (m.d 0 1) (by simp) with h2018 | h2018
                          · rcases p2008_3 (m.d 0 2) (by simp) with h2019 | h2019
                            · linarith only [h0, h2019, hlam]
                            · rcases p2008_3 (m.d 0 3) (by simp) with h2021 | h2021
                              · linarith only [h1, h2021, hlam]
                              · linarith only [h1640, h2021, hlam]
                          · linarith only [h2, h2018, hlam]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          rcases p2008_3 (m.d 0 1) (by simp) with h2025 | h2025
                          · rcases p2008_3 (m.d 0 2) (by simp) with h2026 | h2026
                            · linarith only [h0, h2026, hlam]
                            · rcases p2008_3 (m.d 0 3) (by simp) with h2028 | h2028
                              · linarith only [h1, h2028, hlam]
                              · linarith only [h1641, h2028, hlam]
                          · linarith only [h2025, h3, hlam]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h0, hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h4, hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h1160, hlam, p2008_1]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h1498, hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h1, hlam, p2008_1]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          rcases p2008_3 (m.d 0 1) (by simp) with h2038 | h2038
                          · rcases p2008_3 (m.d 0 2) (by simp) with h2039 | h2039
                            · linarith only [h2039, h4, hlam]
                            · rcases p2008_3 (m.d 0 3) (by simp) with h2041 | h2041
                              · rcases p2008_3 (m.d 0 4) (by simp) with h2042 | h2042
                                · linarith only [h1640, h2042, hlam]
                                · linarith only [h1160, h2042, hlam]
                              · linarith only [h2041, h4, hlam]
                          · linarith only [h0, h2038, hlam]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          rcases p2008_3 (m.d 0 1) (by simp) with h2048 | h2048
                          · rcases p2008_3 (m.d 0 2) (by simp) with h2049 | h2049
                            · linarith only [h2049, h4, hlam]
                            · rcases p2008_3 (m.d 0 3) (by simp) with h2051 | h2051
                              · rcases p2008_3 (m.d 0 4) (by simp) with h2052 | h2052
                                · linarith only [h1640, h2052, hlam]
                                · rcases p2008_3 (m.d 0 5) (by simp) with h2054 | h2054
                                  · linarith only [h1641, h2054, hlam]
                                  · linarith only [h1642, h2054, hlam]
                              · linarith only [h1640, h2051, hlam]
                          · linarith only [h2, h2048, hlam]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          rcases p2008_3 (m.d 0 1) (by simp) with h2059 | h2059
                          · rcases p2008_3 (m.d 0 2) (by simp) with h2060 | h2060
                            · linarith only [h2060, h4, hlam]
                            · rcases p2008_3 (m.d 0 3) (by simp) with h2062 | h2062
                              · rcases p2008_3 (m.d 0 4) (by simp) with h2063 | h2063
                                · linarith only [h1640, h2063, hlam]
                                · rcases p2008_3 (m.d 0 5) (by simp) with h2065 | h2065
                                  · linarith only [h1641, h2065, hlam]
                                  · rcases h3bigk with h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1, h1887, h2006, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1, u1elo0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h4, hlam, p2067_1]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      rcases p2067_3 (m.d 0 3) (by simp) with h2071 | h2071
                                      · rcases p2067_3 (m.d 1 3) (by simp) with h2072 | h2072
                                        · linarith only [h1, h2072, hlam]
                                        · linarith only [h1886, h2072, hlam]
                                      · linarith only [h2071, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      rcases p2067_3 (m.d 0 3) (by simp) with h2076 | h2076
                                      · rcases p2067_3 (m.d 1 3) (by simp) with h2077 | h2077
                                        · linarith only [h1, h2077, hlam]
                                        · linarith only [h1887, h2077, hlam]
                                      · linarith only [h2076, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1882, hlam, p2067_1]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1, u1elo0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1, h2006, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1, u1elo0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2008_1, p2067_1]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      rcases p2067_3 (m.d 0 3) (by simp) with h2087 | h2087
                                      · linarith only [h2087, h4, hlam]
                                      · linarith only [h1, h2087, hlam]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      rcases p2067_3 (m.d 0 3) (by simp) with h2091 | h2091
                                      · linarith only [h2091, h4, hlam]
                                      · linarith only [h1640, h2091, hlam]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      rcases p2067_3 (m.d 0 3) (by simp) with h2094 | h2094
                                      · linarith only [h2094, h4, hlam]
                                      · linarith only [h1641, h2094, hlam]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1640, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1886, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1890, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h2006, hlam, p2067_1]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1641, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1887, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1891, hlam, p2067_0]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [h1887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1, u1elo2]
                                    · have p2067_0 := h2067c.1
                                      have p2067_1 := h2067c.2.1
                                      have p2067_2 := h2067c.2.2.1
                                      have p2067_3 := h2067c.2.2.2
                                      linarith only [hlam, p2067_0]
                              · linarith only [h1641, h2062, hlam]
                          · linarith only [h2059, h3, hlam]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h2, hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h0, h1160, h1892, hc12, hc45, hlam, hphi, ht23, ht34, p2008_1]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h1640, hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h1642, hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h3, hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          rcases p2008_3 (m.d 0 1) (by simp) with h2115 | h2115
                          · rcases p2008_3 (m.d 0 2) (by simp) with h2116 | h2116
                            · linarith only [h1498, h2116, hlam]
                            · rcases p2008_3 (m.d 0 3) (by simp) with h2118 | h2118
                              · rcases p2008_3 (m.d 0 4) (by simp) with h2119 | h2119
                                · linarith only [h1642, h2119, hlam]
                                · linarith only [h1160, h2119, hlam]
                              · linarith only [h2118, h4, hlam]
                          · linarith only [h0, h2115, hlam]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [h1641, hlam, p2008_0]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          rcases p2008_3 (m.d 0 1) (by simp) with h2125 | h2125
                          · rcases p2008_3 (m.d 0 2) (by simp) with h2126 | h2126
                            · linarith only [h1498, h2126, hlam]
                            · rcases p2008_3 (m.d 0 3) (by simp) with h2128 | h2128
                              · rcases p2008_3 (m.d 0 4) (by simp) with h2129 | h2129
                                · linarith only [h1642, h2129, hlam]
                                · rcases p2008_3 (m.d 0 5) (by simp) with h2131 | h2131
                                  · rcases h3bigk with h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c | h2132c
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1, h1887, hc35, hlam, hphi, ht01, ht0b, ht5b, p2132_1, u1elo0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h4, hlam, p2132_1]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      rcases p2132_3 (m.d 0 3) (by simp) with h2136 | h2136
                                      · rcases p2132_3 (m.d 1 3) (by simp) with h2137 | h2137
                                        · linarith only [h1, h2137, hlam]
                                        · linarith only [h1886, h2137, hlam]
                                      · linarith only [h2136, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      rcases p2132_3 (m.d 0 3) (by simp) with h2141 | h2141
                                      · rcases p2132_3 (m.d 1 3) (by simp) with h2142 | h2142
                                        · linarith only [h1, h2142, hlam]
                                        · linarith only [h1887, h2142, hlam]
                                      · linarith only [h2141, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1882, hlam, p2132_1]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2132_1, u1elo0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1, h2006, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2132_1, u1elo0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1641, h1884, h2, hc12, hc23, hlam, hphi, p2008_1, p2132_1]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      rcases p2132_3 (m.d 0 3) (by simp) with h2152 | h2152
                                      · linarith only [h2152, h4, hlam]
                                      · linarith only [h1, h2152, hlam]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      rcases p2132_3 (m.d 0 3) (by simp) with h2156 | h2156
                                      · linarith only [h2156, h4, hlam]
                                      · linarith only [h1640, h2156, hlam]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      rcases p2132_3 (m.d 0 3) (by simp) with h2159 | h2159
                                      · linarith only [h2159, h4, hlam]
                                      · linarith only [h1641, h2159, hlam]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1640, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1886, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1890, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h2006, hlam, p2132_1]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1641, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1887, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1891, hlam, p2132_0]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [h1887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2132_1, u1elo2]
                                    · have p2132_0 := h2132c.1
                                      have p2132_1 := h2132c.2.1
                                      have p2132_2 := h2132c.2.2.1
                                      have p2132_3 := h2132c.2.2.2
                                      linarith only [hlam, p2132_0]
                                  · linarith only [h1642, h2131, hlam]
                              · linarith only [h1640, h2128, hlam]
                          · linarith only [h2, h2125, hlam]
                        · have p2008_0 := h2008c.1
                          have p2008_1 := h2008c.2.1
                          have p2008_2 := h2008c.2.2.1
                          have p2008_3 := h2008c.2.2.2
                          linarith only [hlam, p2008_0]
                  · linarith only [h0, h1887, h1891, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1640, h1890, h4, hlam]
            · linarith only [h1641, h1886, h1887, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2179 | h2179
            · linarith only [h1, h1640, h1886, h2179, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2181 | h2181
              · linarith only [h1640, h1642, h1886, h2181, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2183 | h2183
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2184 | h2184
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2185 | h2185
                    · linarith only [h1640, h1642, h1882, h1886, h2185, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2187 | h2187
                      · linarith only [h1640, h1642, h2187, hlam]
                      · rcases h0bigk with h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          rcases p2189_3 (m.d 0 1) (by simp) with h2191 | h2191
                          · rcases p2189_3 (m.d 0 2) (by simp) with h2192 | h2192
                            · linarith only [h0, h2192, hlam]
                            · rcases p2189_3 (m.d 0 3) (by simp) with h2194 | h2194
                              · linarith only [h1, h2194, hlam]
                              · linarith only [h2194, h4, hlam]
                          · linarith only [h0, h2191, hlam]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1640, h1882, h1886, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2189_1, u1elo0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1640, h1882, h1886, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2189_1, u1elo0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1641, h1882, h1886, h2187, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2189_1, u1elo0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h0, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h4, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1160, hlam, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1498, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1, hlam, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          rcases p2189_3 (m.d 0 1) (by simp) with h2207 | h2207
                          · rcases p2189_3 (m.d 0 2) (by simp) with h2208 | h2208
                            · linarith only [h2208, h4, hlam]
                            · rcases p2189_3 (m.d 0 3) (by simp) with h2210 | h2210
                              · rcases p2189_3 (m.d 0 4) (by simp) with h2211 | h2211
                                · linarith only [h1640, h2211, hlam]
                                · linarith only [h1160, h2211, hlam]
                              · linarith only [h2210, h4, hlam]
                          · linarith only [h0, h2207, hlam]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1640, h1882, h1886, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2189_1, u0elo2]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1, h1641, h1882, h1886, h2187, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2189_1, u1elo0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h0, h1160, h2185, hc12, hc45, hlam, hphi, ht23, ht34, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1640, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1642, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h3, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          rcases p2189_3 (m.d 0 1) (by simp) with h2225 | h2225
                          · rcases p2189_3 (m.d 0 2) (by simp) with h2226 | h2226
                            · linarith only [h1498, h2226, hlam]
                            · rcases p2189_3 (m.d 0 3) (by simp) with h2228 | h2228
                              · rcases p2189_3 (m.d 0 4) (by simp) with h2229 | h2229
                                · linarith only [h1642, h2229, hlam]
                                · linarith only [h1160, h2229, hlam]
                              · linarith only [h2228, h4, hlam]
                          · linarith only [h0, h2225, hlam]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1641, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h1640, h1882, h1886, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2189_1, u0elo4]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
                  · linarith only [h1640, h1882, h1886, h2184, h4, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1640, h2183, h4, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2239 | h2239
    · linarith only [h1640, h1641, h2239, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2241 | h2241
      · linarith only [h0, h1640, h2241, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2243 | h2243
        · linarith only [h0, h1160, h2243, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2245 | h2245
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2246 | h2246
            · linarith only [h1, h1641, h2246, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2248 | h2248
              · linarith only [h0, h1160, h2, h2239, h2248, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2250 | h2250
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2251 | h2251
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2252 | h2252
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2253 | h2253
                      · linarith only [h0, h1, h1160, h2239, h2245, h2253, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          rcases p2255_3 (m.d 0 1) (by simp) with h2257 | h2257
                          · rcases p2255_3 (m.d 0 2) (by simp) with h2258 | h2258
                            · linarith only [h0, h2258, hlam]
                            · rcases p2255_3 (m.d 0 3) (by simp) with h2260 | h2260
                              · linarith only [h1, h2260, hlam]
                              · linarith only [h2260, h4, hlam]
                          · linarith only [h0, h2257, hlam]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h1, h2245, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2255_1, u1elo0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          rcases p2255_3 (m.d 0 1) (by simp) with h2265 | h2265
                          · rcases p2255_3 (m.d 0 2) (by simp) with h2266 | h2266
                            · linarith only [h0, h2266, hlam]
                            · rcases p2255_3 (m.d 0 3) (by simp) with h2268 | h2268
                              · linarith only [h1, h2268, hlam]
                              · linarith only [h1640, h2268, hlam]
                          · linarith only [h2, h2265, hlam]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h1, h1641, h2245, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2255_1, u1elo0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h0, hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h4, hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h1160, hlam, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h1498, hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h1, hlam, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h0, h1641, h2250, h2252, h2253, hc12, hc23, hlam, hphi, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h0, h1160, h1641, h2250, h2252, h2253, hc12, hc23, hlam, hphi, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h1641, hlam, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h2, hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h0, h1640, h1641, h2250, h2252, h2253, hc12, hc23, hlam, hphi, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h1640, hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h2239, hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h3, hlam, p2255_0]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h0, h1641, h2250, h2252, h2253, hc12, hc23, hlam, hphi, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h1, h1641, h2245, h2250, h2252, h2253, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [h0, h1160, h1641, h2250, h2252, h2253, hc12, hc23, hlam, hphi, p2255_1]
                        · have p2255_0 := h2255c.1
                          have p2255_1 := h2255c.2.1
                          have p2255_2 := h2255c.2.2.1
                          have p2255_3 := h2255c.2.2.2
                          linarith only [hlam, p2255_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2293 | h2293
                      · linarith only [h1, h2245, h2252, h2293, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          rcases p2295_3 (m.d 0 1) (by simp) with h2297 | h2297
                          · rcases p2295_3 (m.d 0 2) (by simp) with h2298 | h2298
                            · linarith only [h0, h2298, hlam]
                            · rcases p2295_3 (m.d 0 3) (by simp) with h2300 | h2300
                              · linarith only [h1, h2300, hlam]
                              · linarith only [h2300, h4, hlam]
                          · linarith only [h0, h2297, hlam]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h1, h2245, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2295_1, u1elo0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          rcases p2295_3 (m.d 0 1) (by simp) with h2305 | h2305
                          · rcases p2295_3 (m.d 0 2) (by simp) with h2306 | h2306
                            · linarith only [h0, h2306, hlam]
                            · rcases p2295_3 (m.d 0 3) (by simp) with h2308 | h2308
                              · linarith only [h1, h2308, hlam]
                              · linarith only [h1640, h2308, hlam]
                          · linarith only [h2, h2305, hlam]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h1, h1641, h2245, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2295_1, u1elo0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h0, hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h4, hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h1160, hlam, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h1498, hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h1, hlam, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h0, h1641, h2251, hc12, hc25, hlam, hphi, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h0, h1160, h1641, h2251, hc12, hc25, hlam, hphi, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h1641, hlam, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h2, hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h0, h1160, h2252, hc12, hc45, hlam, hphi, ht23, ht34, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h1640, hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h2239, hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h3, hlam, p2295_0]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h0, h1641, h2251, hc12, hc23, hlam, hphi, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h0, h1641, h2251, h4, hc12, hc23, hlam, hphi, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [h0, h1160, h1641, h2251, hc12, hc23, hlam, hphi, p2295_1]
                        · have p2295_0 := h2295c.1
                          have p2295_1 := h2295c.2.1
                          have p2295_2 := h2295c.2.2.1
                          have p2295_3 := h2295c.2.2.2
                          linarith only [hlam, p2295_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2333 | h2333
                    · linarith only [h0, h1160, h2239, h2250, h2251, h2333, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2335 | h2335
                      · linarith only [h0, h1, h1160, h2245, h2333, h2335, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c | h2337c
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          rcases p2337_3 (m.d 0 1) (by simp) with h2339 | h2339
                          · rcases p2337_3 (m.d 0 2) (by simp) with h2340 | h2340
                            · linarith only [h0, h2340, hlam]
                            · rcases p2337_3 (m.d 0 3) (by simp) with h2342 | h2342
                              · linarith only [h1, h2342, hlam]
                              · linarith only [h2342, h4, hlam]
                          · linarith only [h0, h2339, hlam]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h1640, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2337_1, u1elo0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          rcases p2337_3 (m.d 0 1) (by simp) with h2347 | h2347
                          · rcases p2337_3 (m.d 0 2) (by simp) with h2348 | h2348
                            · linarith only [h0, h2348, hlam]
                            · rcases p2337_3 (m.d 0 3) (by simp) with h2350 | h2350
                              · linarith only [h1, h2350, hlam]
                              · linarith only [h1640, h2350, hlam]
                          · linarith only [h2, h2347, hlam]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h1, h1641, h2245, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2337_1, u1elo0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h0, hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h4, hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h1160, hlam, p2337_1]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h1498, hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h1, hlam, p2337_1]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h0, h2251, h2335, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2337_1]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h0, h1160, h2251, h2335, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2337_1]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h1641, hlam, p2337_1]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h2, hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h0, h1640, h2251, h2335, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2337_1]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h1640, hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h2239, hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h3, hlam, p2337_0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          rcases p2337_3 (m.d 0 1) (by simp) with h2371 | h2371
                          · rcases p2337_3 (m.d 0 2) (by simp) with h2372 | h2372
                            · linarith only [h1498, h2372, hlam]
                            · rcases p2337_3 (m.d 0 3) (by simp) with h2374 | h2374
                              · linarith only [h1641, h2374, hlam]
                              · linarith only [h2374, h4, hlam]
                          · linarith only [h0, h2371, hlam]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [h1640, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2337_1, u1elo0]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          rcases p2337_3 (m.d 0 1) (by simp) with h2379 | h2379
                          · rcases p2337_3 (m.d 0 2) (by simp) with h2380 | h2380
                            · linarith only [h1498, h2380, hlam]
                            · rcases p2337_3 (m.d 0 3) (by simp) with h2382 | h2382
                              · linarith only [h1641, h2382, hlam]
                              · linarith only [h1640, h2382, hlam]
                          · linarith only [h2, h2379, hlam]
                        · have p2337_0 := h2337c.1
                          have p2337_1 := h2337c.2.1
                          have p2337_2 := h2337c.2.2.1
                          have p2337_3 := h2337c.2.2.2
                          linarith only [hlam, p2337_0]
                · linarith only [h1, h2245, h2250, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h1640, h1641, h2245, hc13, hc35, hlam, hphi]

end R2N4
