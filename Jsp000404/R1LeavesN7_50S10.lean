import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x1_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1367 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1500 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1645 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1646 | h1646
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1647 | h1647
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1648 | h1648
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1649 | h1649
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1650 | h1650
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1651 | h1651
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1652 | h1652
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1653 | h1653
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1654 | h1654
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1655 | h1655
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1656 | h1656
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1657 | h1657
                        · rcases h5bigk with h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1500, hlam, p1658_1]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1648, h1655, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi4]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1645, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi4]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            rcases p1658_3 (m.d 0 5) (by simp) with h1663 | h1663
                            · rcases p1658_3 (m.d 1 5) (by simp) with h1664 | h1664
                              · rcases p1658_3 (m.d 2 5) (by simp) with h1665 | h1665
                                · linarith only [h1645, h1665, hlam]
                                · linarith only [h1656, h1665, hlam]
                              · linarith only [h1653, h1664, hlam]
                            · linarith only [h1648, h1663, hlam]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1500, h1649, h1651, h1653, hc01, hc12, hlam, hphi, p1658_1]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1649, h1651, h1653, h1655, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi4]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1649, h1651, h1653, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi4]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            rcases p1658_3 (m.d 0 5) (by simp) with h1674 | h1674
                            · linarith only [h1500, h1674, hlam]
                            · linarith only [h1648, h1674, hlam]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1645, hlam, p1658_1]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1650, hlam, p1658_1]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1645, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi4]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1649, h1654, h1656, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1658_1]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1647, hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1652, hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1655, hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1646, h1657, hc03, hc45, hlam, hphi, ht0b, ht5b, p1658_1]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1648, hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1653, hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1656, hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [h1657, hlam, p1658_0]
                          · have p1658_0 := h1658c.1
                            have p1658_1 := h1658c.2.1
                            have p1658_2 := h1658c.2.2.1
                            have p1658_3 := h1658c.2.2.2
                            linarith only [hlam, p1658_0]
                        · linarith only [h1649, h1654, h1656, h1657, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1693 | h1693
                        · linarith only [h1649, h1654, h1655, h1656, h1693, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases h5bigk with h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1500, hlam, p1695_1]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1654, h1656, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1695_1, u3ehi3]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1500, h1649, h1651, h1653, h1693, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1695_1, u3ehi3]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1500, h1649, h1651, h1653, h1654, h1656, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1695_1, u3ehi3]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1500, h1649, h1651, h1653, hc01, hc12, hlam, hphi, p1695_1]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1649, h1651, h1653, h1654, h1656, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1695_1, u3ehi3]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1649, h1651, h1653, h1693, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1695_1, u3ehi3]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1649, h1651, h1653, h1654, h1656, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1695_1, u3ehi3]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1645, hlam, p1695_1]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1650, hlam, p1695_1]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1693, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1695_1, u3ehi3]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1656, hlam, p1695_1]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1647, hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1652, hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1655, hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1693, hlam, p1695_1]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1648, hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1653, hlam, p1695_0]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1367, h1646, h1648, h1649, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1695_1]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [h1648, h1693, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1695_1, u3ehi3]
                          · have p1695_0 := h1695c.1
                            have p1695_1 := h1695c.2.1
                            have p1695_2 := h1695c.2.2.1
                            have p1695_3 := h1695c.2.2.2
                            linarith only [hlam, p1695_0]
                    · linarith only [h1654, h1655, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1722 | h1722
                    · linarith only [h1654, h1722, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1724 | h1724
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1725 | h1725
                        · rcases h5bigk with h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1500, hlam, p1726_1]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1722, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1726_1, u3ehi2]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1500, h1649, h1651, h1653, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1726_1, u3ehi4]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            rcases p1726_3 (m.d 0 5) (by simp) with h1731 | h1731
                            · rcases p1726_3 (m.d 1 5) (by simp) with h1732 | h1732
                              · rcases p1726_3 (m.d 2 5) (by simp) with h1733 | h1733
                                · linarith only [h1645, h1733, hlam]
                                · linarith only [h1724, h1733, hlam]
                              · linarith only [h1653, h1732, hlam]
                            · linarith only [h1648, h1731, hlam]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1500, h1649, h1651, h1653, hc01, hc12, hlam, hphi, p1726_1]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1649, h1651, h1653, h1722, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1726_1, u3ehi2]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1649, h1651, h1653, h1722, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1726_1, u3ehi2]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            rcases p1726_3 (m.d 0 5) (by simp) with h1742 | h1742
                            · linarith only [h1500, h1742, hlam]
                            · linarith only [h1648, h1742, hlam]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1645, hlam, p1726_1]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1650, hlam, p1726_1]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1722, hlam, p1726_1]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h0, h1645, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1726_1]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1647, hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1652, hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1367, h1647, h1649, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1726_1]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1367, h1646, h1649, h1725, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1726_1]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1648, hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1653, hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1724, hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [h1725, hlam, p1726_0]
                          · have p1726_0 := h1726c.1
                            have p1726_1 := h1726c.2.1
                            have p1726_2 := h1726c.2.2.1
                            have p1726_3 := h1726c.2.2.2
                            linarith only [hlam, p1726_0]
                        · linarith only [h1367, h1646, h1648, h1649, h1654, h1725, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1761 | h1761
                        · linarith only [h1654, h1724, h1761, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1367, h1646, h1648, h1649, h1654, h1761, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h1500, h1648, h1653, hlam]
              · linarith only [h1367, h1646, h1652, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1367, h1647, h1651, hc34, hlam, hphi, u3ehi4]
          · linarith only [h0, h1645, h1650, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1768 | h1768
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1769 | h1769
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1770 | h1770
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1771 | h1771
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1772 | h1772
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1773 | h1773
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1774 | h1774
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1775 | h1775
                        · rcases h5bigk with h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1500, hlam, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h0, h1645, h1649, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h0, h1645, h1649, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1776_1, u3ehi4]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h0, h1645, h1649, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1500, h1771, hc01, hc14, hlam, hphi, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1649, h1768, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1649, h1768, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1776_1, u3ehi4]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1649, h1768, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1645, hlam, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1768, hlam, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1776_1, u3ehi4]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1500, h1645, h1649, h1768, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1647, hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1770, hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1773, hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1646, h1775, hc03, hc45, hlam, hphi, ht0b, ht5b, p1776_1]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1648, hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1771, hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1774, hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [h1775, hlam, p1776_0]
                          · have p1776_0 := h1776c.1
                            have p1776_1 := h1776c.2.1
                            have p1776_2 := h1776c.2.2.1
                            have p1776_3 := h1776c.2.2.2
                            linarith only [hlam, p1776_0]
                        · linarith only [h0, h1645, h1649, h1774, h1775, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1803 | h1803
                        · linarith only [h1772, h1774, h1803, hlam]
                        · rcases h5bigk with h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1500, hlam, p1805_1]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1500, h1649, h1768, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1805_1]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1500, h1649, h1768, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u3ehi4]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1500, h1649, h1768, h1772, h1774, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u3ehi3]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1649, h1768, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1805_1]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1649, h1768, h1773, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u3ehi4]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1649, h1768, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u3ehi4]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1649, h1768, h1772, h1774, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u3ehi3]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1645, hlam, p1805_1]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1768, hlam, p1805_1]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u3ehi4]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1774, hlam, p1805_1]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1647, hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1770, hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1773, hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1803, hlam, p1805_1]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1648, hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1771, hlam, p1805_0]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1646, h1648, hc03, hc25, hlam, hphi, ht0b, ht5b, p1805_1]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [h1367, h1646, h1648, h1649, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1805_1, u3ehi4]
                          · have p1805_0 := h1805c.1
                            have p1805_1 := h1805c.2.1
                            have p1805_2 := h1805c.2.2.1
                            have p1805_3 := h1805c.2.2.2
                            linarith only [hlam, p1805_0]
                    · linarith only [h0, h1649, h1773, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h1500, h1646, h1649, h1768, h1772, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h1500, h1648, h1771, hlam]
              · linarith only [h1367, h1646, h1770, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1367, h1646, h1769, hlam]
          · linarith only [h0, h1645, h1768, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1837 | h1837
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1838 | h1838
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1839 | h1839
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1840 | h1840
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1841 | h1841
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1842 | h1842
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1843 | h1843
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1844 | h1844
                      · linarith only [h1646, h1648, h1837, h1842, h1844, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1846 | h1846
                        · linarith only [h1646, h1648, h1846, hlam]
                        · rcases h5bigk with h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [hlam, p1848_0]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1500, hlam, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1842, h1844, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1648, h1839, h1841, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1648, hlam, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1500, hc01, hc15, hlam, hphi, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [hlam, p1848_0]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1838, h1842, h1844, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1837, h1840, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi4]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1646, h1648, h1837, h1839, h1841, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1645, hlam, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1838, hlam, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [hlam, p1848_0]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1645, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi4]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1844, hlam, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1647, hlam, p1848_0]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1840, hlam, p1848_0]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1843, hlam, p1848_0]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [hlam, p1848_0]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1846, hlam, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1500, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1841, hlam, p1848_0]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1837, h1839, h1841, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1848_1]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [h1837, h1839, h1841, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi4]
                          · have p1848_0 := h1848c.1
                            have p1848_1 := h1848c.2.1
                            have p1848_2 := h1848c.2.2.1
                            have p1848_3 := h1848c.2.2.2
                            linarith only [hlam, p1848_0]
                    · linarith only [h1842, h1843, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1646, h1648, h1837, h1839, h1841, h1842, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1876 | h1876
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1877 | h1877
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1878 | h1878
                      · linarith only [h1646, h1648, h1837, h1876, h1878, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1880 | h1880
                        · linarith only [h1646, h1648, h1880, hlam]
                        · rcases h5bigk with h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1500, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1877, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1882_1, u3ehi4]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1647, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1882_1, u3ehi4]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1648, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1500, h1841, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1841, h1877, hc45, hlam, hphi, ht34, p1882_1, u3ehi4]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1841, hc45, hlam, hphi, ht34, p1882_1, u3ehi4]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1841, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1645, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1838, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1645, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1882_1, u3ehi4]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1878, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1647, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1840, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1877, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1880, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1500, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1500, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1877, hc45, hlam, hphi, ht34, p1882_1, u3ehi4]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1882_1, u3ehi4]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                    · linarith only [h1367, h1647, h1837, h1876, h1877, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1646, h1648, h1876, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1367, h1646, h1840, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1367, h1646, h1839, hlam]
          · linarith only [h0, h1645, h1838, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1913 | h1913
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1914 | h1914
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1915 | h1915
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1916 | h1916
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1917 | h1917
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1918 | h1918
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1919 | h1919
                      · linarith only [h1645, h1648, h1919, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1921 | h1921
                        · linarith only [h1646, h1648, h1921, hlam]
                        · rcases h5bigk with h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c | h1923c
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [hlam, p1923_0]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1500, hlam, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1648, h1837, h1914, h1916, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1648, h1837, h1914, h1916, h1921, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1923_1, u3ehi3]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1648, hlam, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1500, hc01, hc15, hlam, hphi, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [hlam, p1923_0]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1837, h1913, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1837, h1913, h1921, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1923_1, u3ehi3]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1837, h1913, h1919, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1645, hlam, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1913, hlam, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [hlam, p1923_0]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1921, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1923_1, u3ehi3]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1919, hlam, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1647, hlam, p1923_0]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1915, hlam, p1923_0]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1918, hlam, p1923_0]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [hlam, p1923_0]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1921, hlam, p1923_1]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1647, h1921, hc45, hlam, hphi, ht34, p1923_1, u3ehi3]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1916, hlam, p1923_0]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1837, h1914, h1916, h1918, h1921, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1923_1, u3ehi3]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [h1837, h1914, h1916, h1921, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1923_1, u3ehi3]
                          · have p1923_0 := h1923c.1
                            have p1923_1 := h1923c.2.1
                            have p1923_2 := h1923c.2.2.1
                            have p1923_3 := h1923c.2.2.2
                            linarith only [hlam, p1923_0]
                    · linarith only [h0, h1647, h1837, h1918, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h1646, h1648, h1837, h1914, h1916, h1917, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1951 | h1951
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1952 | h1952
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1953 | h1953
                      · linarith only [h1500, h1645, h1916, h1953, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1955 | h1955
                        · linarith only [h0, h1645, h1837, h1916, h1951, h1953, h1955, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases h5bigk with h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c | h1957c
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [hlam, p1957_0]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1500, hlam, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h0, h1645, h1837, h1951, h1953, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1957_1, u3ehi3]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h0, h1645, h1837, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1648, hlam, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1837, h1913, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [hlam, p1957_0]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1837, h1913, h1951, h1953, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1957_1, u3ehi3]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1837, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1957_1, u3ehi4]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1916, hlam, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1645, hlam, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1913, hlam, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [hlam, p1957_0]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1645, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1957_1, u3ehi4]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1953, hlam, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1647, hlam, p1957_0]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1915, hlam, p1957_0]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1952, hlam, p1957_0]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [hlam, p1957_0]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1955, hlam, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1500, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1500, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1957_1]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [h1952, hc45, hlam, hphi, ht34, p1957_1, u3ehi4]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1957_1, u3ehi4]
                          · have p1957_0 := h1957c.1
                            have p1957_1 := h1957c.2.1
                            have p1957_2 := h1957c.2.2.1
                            have p1957_3 := h1957c.2.2.2
                            linarith only [hlam, p1957_0]
                    · linarith only [h0, h1837, h1952, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h1645, h1646, h1648, h1837, h1951, hlam]
              · linarith only [h0, h1367, h1645, h1647, h1837, h1915, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h1367, h1646, h1914, hlam]
          · linarith only [h0, h1645, h1913, hlam]
    · linarith only [h1646, h1647, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1989 | h1989
    · linarith only [h1646, h1989, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1991 | h1991
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1992 | h1992
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1993 | h1993
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1994 | h1994
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1995 | h1995
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1996 | h1996
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1997 | h1997
                  · linarith only [h1646, h1992, h1997, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1999 | h1999
                    · linarith only [h1989, h1994, h1997, h1999, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2001 | h2001
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2002 | h2002
                        · rcases h5bigk with h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1500, hlam, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1646, h1991, h1992, h1994, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1989, hlam, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1646, h1991, h1992, h1994, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1500, h1992, h1994, h1996, hc01, hc12, hlam, hphi, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1992, h1994, h1996, h1999, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2003_1, u3ehi2]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1992, h1994, h1996, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2003_1, u3ehi4]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            rcases p2003_3 (m.d 0 5) (by simp) with h2013 | h2013
                            · linarith only [h1500, h2013, hlam]
                            · linarith only [h1991, h2013, hlam]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1645, hlam, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1993, hlam, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1999, hlam, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h0, h1645, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1500, hc01, hc35, hlam, hphi, ht12, ht23, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1995, hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1992, h1995, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1992, h1994, h2002, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2003_1]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1991, hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h1996, hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h2001, hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [h2002, hlam, p2003_0]
                          · have p2003_0 := h2003c.1
                            have p2003_1 := h2003c.2.1
                            have p2003_2 := h2003c.2.2.1
                            have p2003_3 := h2003c.2.2.2
                            linarith only [hlam, p2003_0]
                        · linarith only [h1646, h2002, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h1646, h1991, h1997, h2001, hc34, hlam, hphi, u3ehi2]
                · linarith only [h1646, h1991, h1994, h1996, hlam]
              · linarith only [h1994, h1995, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2035 | h2035
              · linarith only [h1994, h2035, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2037 | h2037
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2038 | h2038
                  · linarith only [h1367, h1994, h2038, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2040 | h2040
                    · linarith only [h1367, h1992, h2035, h2040, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2042 | h2042
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2043 | h2043
                        · rcases h5bigk with h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [hlam, p2044_0]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h1500, hlam, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h2040, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2044_1, u3ehi2]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h1989, hlam, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            rcases p2044_3 (m.d 0 5) (by simp) with h2049 | h2049
                            · rcases p2044_3 (m.d 1 5) (by simp) with h2050 | h2050
                              · rcases p2044_3 (m.d 2 5) (by simp) with h2051 | h2051
                                · linarith only [h1645, h2051, hlam]
                                · linarith only [h2042, h2051, hlam]
                              · linarith only [h2037, h2050, hlam]
                            · linarith only [h1991, h2049, hlam]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h1500, h2037, hc01, hc14, hlam, hphi, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [hlam, p2044_0]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h2037, h2040, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2044_1, u3ehi2]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h2035, hlam, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            rcases p2044_3 (m.d 0 5) (by simp) with h2060 | h2060
                            · linarith only [h1500, h2060, hlam]
                            · linarith only [h1991, h2060, hlam]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h1645, hlam, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h1993, hlam, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [hlam, p2044_0]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h2040, hlam, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h0, h1645, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h1500, h2043, hc01, hc34, hlam, hphi, ht12, ht23, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h1500, h2043, hc01, hc34, hlam, hphi, ht12, ht23, p2044_1]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h2040, h2043, hc34, hlam, hphi, p2044_1, u3ehi2]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [hlam, p2044_0]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            rcases p2044_3 (m.d 0 5) (by simp) with h2072 | h2072
                            · linarith only [h1989, h2072, hlam]
                            · linarith only [h1991, h2072, hlam]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h1991, hlam, p2044_0]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h2037, hlam, p2044_0]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h2042, hlam, p2044_0]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [h2043, hlam, p2044_0]
                          · have p2044_0 := h2044c.1
                            have p2044_1 := h2044c.2.1
                            have p2044_2 := h2044c.2.2.1
                            have p2044_3 := h2044c.2.2.2
                            linarith only [hlam, p2044_0]
                        · linarith only [h1646, h2043, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h1646, h1991, h2038, h2042, hc34, hlam, hphi, u3ehi2]
                · linarith only [h1646, h1991, h1994, h2037, hc34, hlam, hphi, u3ehi1]
          · linarith only [h0, h1645, h1993, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2084 | h2084
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2085 | h2085
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2086 | h2086
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2087 | h2087
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2088 | h2088
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2089 | h2089
                    · linarith only [h1645, h1989, h2089, hlam]
                    · linarith only [h1992, h2085, h2089, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1989, h1992, h2084, h2085, h2086, h2088, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h1646, h2085, h2087, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h1646, h2085, h2086, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2095 | h2095
              · linarith only [h2085, h2095, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1992, h2084, h2095, hlam]
          · linarith only [h0, h1645, h2084, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2099 | h2099
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2100 | h2100
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2101 | h2101
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2102 | h2102
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2103 | h2103
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2104 | h2104
                  · linarith only [h1646, h2099, h2104, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2106 | h2106
                    · linarith only [h2104, h2106, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2108 | h2108
                      · linarith only [h1646, h1991, h2099, h2101, h2104, h2108, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2110 | h2110
                        · linarith only [h1646, h1991, h2099, h2101, h2110, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1646, h2103, h2110, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h1646, h2101, h2103, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h1646, h2101, h2102, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2115 | h2115
              · linarith only [h2101, h2115, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2117 | h2117
                · linarith only [h1646, h1991, h2101, h2117, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2119 | h2119
                  · linarith only [h1646, h2099, h2119, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2121 | h2121
                    · linarith only [h2099, h2101, h2121, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2123 | h2123
                      · linarith only [h1367, h2101, h2117, h2123, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2125 | h2125
                        · linarith only [h1367, h2101, h2117, h2125, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1646, h2125, hc45, hlam, hphi, ht34, u3ehi0]
          · linarith only [h0, h1645, h2100, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2129 | h2129
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2130 | h2130
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2131 | h2131
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2132 | h2132
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2133 | h2133
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2134 | h2134
                    · linarith only [h0, h1645, h1989, h2099, h2134, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h2099, h2134, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h1646, h1991, h2099, h2130, h2132, h2133, hc34, hlam, hphi, u3ehi0]
                · linarith only [h1646, h2130, h2132, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h1646, h2130, h2131, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2140 | h2140
              · linarith only [h2130, h2140, hc34, hlam, hphi, u3ehi4]
              · linarith only [h2099, h2129, h2140, hlam]
          · linarith only [h0, h1645, h2129, hlam]

end R2N4
