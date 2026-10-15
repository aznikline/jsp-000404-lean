import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1668 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1669 | h1669
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1670 | h1670
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1671 | h1671
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1672 | h1672
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1673 | h1673
          · linarith only [h0, h1668, h1673, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1675 | h1675
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1676 | h1676
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1677 | h1677
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1678 | h1678
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1679 | h1679
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1680 | h1680
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1681 | h1681
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1682 | h1682
                          · rcases h0bigk with h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h0, h1675, h1679, h1682, hc01, hc45, hlam, hphi, ht0b, ht5b, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h0, h1675, h1679, h1682, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1668, h1679, h1682, hc01, hc45, hlam, hphi, ht0b, ht5b, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              rcases p1683_3 (m.d 0 1) (by simp) with h1688 | h1688
                              · rcases p1683_3 (m.d 0 2) (by simp) with h1689 | h1689
                                · linarith only [h0, h1689, hlam]
                                · linarith only [h1669, h1689, hlam]
                              · linarith only [h1688, h3, hlam]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h0, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h4, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1675, h1679, h1682, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1675, h1679, h1682, h2, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              rcases p1683_3 (m.d 0 1) (by simp) with h1702 | h1702
                              · rcases p1683_3 (m.d 0 2) (by simp) with h1703 | h1703
                                · linarith only [h1703, h4, hlam]
                                · linarith only [h1669, h1703, hlam]
                              · linarith only [h1702, h3, hlam]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h2, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1668, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1670, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1668, h1676, h1680, h1682, h3, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h3, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1669, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1671, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1672, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                          · linarith only [h0, h1675, h1681, h1682, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1718 | h1718
                          · linarith only [h1679, h1681, h1718, hlam]
                          · rcases h0bigk with h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1668, h1678, h1679, h1681, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1668, h1678, h1679, h1681, h2, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1678, h1679, h1681, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1678, h1679, h1681, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h0, hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h4, hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1678, h1679, h1681, h2, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1678, h1679, h1681, h3, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1, hlam, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1678, h1679, h1681, h2, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1678, h1679, h1681, h3, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h2, hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1668, hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1670, hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1668, h1678, h1679, h1681, h3, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h3, hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1669, hlam, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1671, hlam, p1720_0]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [h1672, hlam, p1720_1]
                            · have p1720_0 := h1720c.1
                              have p1720_1 := h1720c.2.1
                              have p1720_2 := h1720c.2.2.1
                              have p1720_3 := h1720c.2.2.2
                              linarith only [hlam, p1720_0]
                      · linarith only [h1680, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1670, h1679, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1748 | h1748
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1749 | h1749
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1750 | h1750
                        · linarith only [h1675, h1678, h1750, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1752 | h1752
                          · linarith only [h1675, h1678, h1748, h1752, hlam]
                          · rcases h0bigk with h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1668, h1672, h1675, h1678, h1748, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1668, h1672, h1675, h1678, h1748, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1672, h1675, h1678, h1748, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1672, h1675, h1678, h1748, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h0, hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h4, hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1672, h1675, h1678, h1748, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1, hlam, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1672, h1675, h1678, h1748, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1672, h1675, h1678, h1748, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h2, hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1668, hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1670, hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1668, h1672, h1675, h1678, h1748, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h3, hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1669, hlam, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1671, hlam, p1754_0]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [h1672, hlam, p1754_1]
                            · have p1754_0 := h1754c.1
                              have p1754_1 := h1754c.2.1
                              have p1754_2 := h1754c.2.2.1
                              have p1754_3 := h1754c.2.2.2
                              linarith only [hlam, p1754_0]
                      · linarith only [h1749, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1668, h1672, h1675, h1678, h1748, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1673, h1675, h1677, hlam]
              · linarith only [h1675, h1676, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1668, h1675, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1785 | h1785
          · linarith only [h0, h1668, h1785, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1787 | h1787
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1788 | h1788
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1789 | h1789
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1790 | h1790
                  · linarith only [h1672, h1790, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1792 | h1792
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1793 | h1793
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1794 | h1794
                        · linarith only [h0, h1672, h1787, h1794, h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1796 | h1796
                          · linarith only [h1672, h1787, h1792, h1796, h2, hlam]
                          · rcases h0bigk with h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h0, h1788, h1794, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1798_1]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h1, h1785, h1788, h1792, h1794, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1798_1]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              rcases p1798_3 (m.d 0 1) (by simp) with h1802 | h1802
                              · rcases p1798_3 (m.d 0 2) (by simp) with h1803 | h1803
                                · linarith only [h0, h1803, hlam]
                                · linarith only [h1668, h1803, hlam]
                              · linarith only [h1802, h2, hlam]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              rcases p1798_3 (m.d 0 1) (by simp) with h1807 | h1807
                              · rcases p1798_3 (m.d 0 2) (by simp) with h1808 | h1808
                                · linarith only [h0, h1808, hlam]
                                · linarith only [h1669, h1808, hlam]
                              · linarith only [h1807, h3, hlam]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h0, hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h4, hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1798_1]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1798_1]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h1, hlam, p1798_1]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p1798_1]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              rcases p1798_3 (m.d 0 1) (by simp) with h1820 | h1820
                              · rcases p1798_3 (m.d 0 2) (by simp) with h1821 | h1821
                                · linarith only [h1821, h4, hlam]
                                · linarith only [h1668, h1821, hlam]
                              · linarith only [h1820, h2, hlam]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              rcases p1798_3 (m.d 0 1) (by simp) with h1825 | h1825
                              · rcases p1798_3 (m.d 0 2) (by simp) with h1826 | h1826
                                · linarith only [h1826, h4, hlam]
                                · linarith only [h1669, h1826, hlam]
                              · linarith only [h1825, h3, hlam]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h2, hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h1668, hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h1670, hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h1672, hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h3, hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h1669, hlam, p1798_1]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h1671, hlam, p1798_0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [h1787, h1792, h2, hc34, hlam, hphi, ht45, p1798_1, u5elo0]
                            · have p1798_0 := h1798c.1
                              have p1798_1 := h1798c.2.1
                              have p1798_2 := h1798c.2.2.1
                              have p1798_3 := h1798c.2.2.2
                              linarith only [hlam, p1798_0]
                      · linarith only [h1, h1785, h1788, h1793, h4, hc25, hlam, hphi, u5elo3]
                    · linarith only [h0, h1670, h1787, h1792, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1670, h1672, h1785, h1787, h1789, hc24, hlam, hphi, ht45, u5elo4]
              · linarith only [h1787, h1788, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1668, h1787, h4, hc12, hc23, hlam, hphi]
      · linarith only [h1669, h1671, h4, hc25, hlam, hphi, u5elo3]
    · linarith only [h1668, h1670, h4, hlam]
  · linarith only [h1668, h1669, hc24, hlam, hphi, ht45, u5elo2]

end R2N4
