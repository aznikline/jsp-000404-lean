import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S0
import Jsp000404.R1LeavesN7_21S1
import Jsp000404.R1LeavesN7_21S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h672 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h951 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1096 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h1584 | h1584
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1585 | h1585
    · linarith only [h0, h1585, h2, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1587 | h1587
      · linarith only [h0, h1587, h672, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1589 | h1589
        · linarith only [h0, h1589, h951, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1591 | h1591
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1592 | h1592
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1593 | h1593
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1594 | h1594
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1595 | h1595
                  · rcases h2bigk with h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h1096, h1592, h1595, h2, hc12, hc23, hlam, hphi, p1596_1]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h2, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h672, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h951, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h0, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h1585, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h1587, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h1589, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      rcases p1596_3 (m.d 0 2) (by simp) with h1607 | h1607
                      · linarith only [h1607, hlam, p1596_0]
                      · rcases p1596_3 (m.d 1 2) (by simp) with h1609 | h1609
                        · linarith only [h1585, h1609, hlam]
                        · rcases p1596_3 (m.d 2 3) (by simp) with h1611 | h1611
                          · rcases p1596_3 (m.d 2 4) (by simp) with h1612 | h1612
                            · linarith only [h1592, h1612, hlam]
                            · linarith only [h1612, h672, hlam]
                          · linarith only [h1611, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      rcases p1596_3 (m.d 0 2) (by simp) with h1616 | h1616
                      · linarith only [h1616, h2, hlam]
                      · linarith only [h0, h1616, hlam]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h1096, h1593, h1594, h2, hc02, hc23, hlam, hphi, p1596_1]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h0, h1096, h1593, h2, hc12, hc23, hlam, hphi, p1596_1]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      rcases p1596_3 (m.d 0 2) (by simp) with h1622 | h1622
                      · linarith only [h1622, hlam, p1596_0]
                      · rcases p1596_3 (m.d 1 2) (by simp) with h1624 | h1624
                        · linarith only [h1587, h1624, hlam]
                        · rcases p1596_3 (m.d 2 3) (by simp) with h1626 | h1626
                          · rcases p1596_3 (m.d 2 4) (by simp) with h1627 | h1627
                            · rcases p1596_3 (m.d 2 5) (by simp) with h1628 | h1628
                              · linarith only [h1594, h1628, hlam]
                              · linarith only [h1628, h951, hlam]
                            · linarith only [h1627, hlam, p1596_0]
                          · linarith only [h1626, h2, hlam]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      rcases p1596_3 (m.d 0 2) (by simp) with h1633 | h1633
                      · linarith only [h1633, h672, hlam]
                      · linarith only [h0, h1633, hlam]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h1592, hlam, p1596_1]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h0, h1096, h1593, h2, hc12, hc24, hlam, hphi, p1596_1]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      rcases p1596_3 (m.d 0 2) (by simp) with h1639 | h1639
                      · linarith only [h1639, hlam, p1596_0]
                      · rcases p1596_3 (m.d 1 2) (by simp) with h1641 | h1641
                        · linarith only [h1589, h1641, hlam]
                        · rcases p1596_3 (m.d 2 3) (by simp) with h1643 | h1643
                          · rcases p1596_3 (m.d 2 4) (by simp) with h1644 | h1644
                            · rcases p1596_3 (m.d 2 5) (by simp) with h1645 | h1645
                              · rcases h5bigk with h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p1646_1, u0elo4]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h951, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1096, hlam, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1584, hc45, hlam, hphi, ht0b, ht5b, p1646_1, u0elo3]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1589, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1, h1096, hc05, hlam, hphi, ht0b, ht5b, p1646_1, u0elo0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p1646_1, u0elo0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h0, h1096, h2, hc12, hc25, hlam, hphi, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1589, hc12, hc25, hlam, hphi, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h0, h1096, h1593, h2, hc12, hc23, hlam, hphi, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  rcases p1646_3 (m.d 0 5) (by simp) with h1661 | h1661
                                  · linarith only [h1661, h951, hlam]
                                  · linarith only [h1584, h1661, hlam]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h0, h1096, h2, hc12, hc35, hlam, hphi, ht23, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1589, h1592, h1595, hc12, hc23, hlam, hphi, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1593, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1592, h1595, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1584, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1591, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1594, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1595, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                              · linarith only [h1645, hlam, p1596_0]
                            · linarith only [h1644, h672, hlam]
                          · linarith only [h1643, h2, hlam]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      rcases p1596_3 (m.d 0 2) (by simp) with h1677 | h1677
                      · linarith only [h1677, h951, hlam]
                      · linarith only [h0, h1677, hlam]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h1593, hlam, p1596_1]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [h1594, hlam, p1596_0]
                    · have p1596_0 := h1596c.1
                      have p1596_1 := h1596c.2.1
                      have p1596_2 := h1596c.2.2.1
                      have p1596_3 := h1596c.2.2.2
                      linarith only [hlam, p1596_0]
                  · linarith only [h1, h1096, h1591, h1595, hlam]
                · linarith only [h0, h1, h1591, h1594, h672, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1685 | h1685
                · linarith only [h1592, h1593, h1685, hlam]
                · linarith only [h1584, h1685, h672, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1688 | h1688
              · linarith only [h0, h1096, h1592, h1688, h2, hc12, hc34, hlam, hphi, ht23]
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
                      linarith only [h1688, h1691, h2, hc12, hc34, hlam, hphi, ht23, p1692_1]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h2, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h672, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h951, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h0, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h1585, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h1587, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h1589, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h1688, h1691, hc02, hc34, hlam, hphi, ht23, p1692_1]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h1688, h1691, hc12, hc34, hlam, hphi, ht23, p1692_1]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h1592, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h1688, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      rcases p1692_3 (m.d 0 2) (by simp) with h1708 | h1708
                      · linarith only [h1708, hlam, p1692_0]
                      · rcases p1692_3 (m.d 1 2) (by simp) with h1710 | h1710
                        · linarith only [h1587, h1710, hlam]
                        · rcases p1692_3 (m.d 2 3) (by simp) with h1712 | h1712
                          · linarith only [h1592, h1712, hlam]
                          · linarith only [h1712, h2, hlam]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      rcases p1692_3 (m.d 0 2) (by simp) with h1715 | h1715
                      · linarith only [h1715, h672, hlam]
                      · linarith only [h0, h1715, hlam]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h0, h1592, h2, hc12, hc34, hlam, hphi, ht23, p1692_1]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h0, h1592, h951, hc12, hc34, hlam, hphi, ht23, p1692_1]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      rcases p1692_3 (m.d 0 2) (by simp) with h1721 | h1721
                      · linarith only [h1721, hlam, p1692_0]
                      · rcases p1692_3 (m.d 1 2) (by simp) with h1723 | h1723
                        · linarith only [h1589, h1723, hlam]
                        · rcases p1692_3 (m.d 2 3) (by simp) with h1725 | h1725
                          · linarith only [h1688, h1725, hlam]
                          · linarith only [h1725, h2, hlam]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      rcases p1692_3 (m.d 0 2) (by simp) with h1728 | h1728
                      · linarith only [h1728, h951, hlam]
                      · linarith only [h0, h1728, hlam]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h0, h2, hc12, hc25, hlam, hphi, p1692_1]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [h1690, hlam, p1692_0]
                    · have p1692_0 := h1692c.1
                      have p1692_1 := h1692c.2.1
                      have p1692_2 := h1692c.2.2.1
                      have p1692_3 := h1692c.2.2.2
                      linarith only [hlam, p1692_0]
                  · linarith only [h1584, h1592, h1691, h672, hlam]
                · linarith only [h1584, h1690, h672, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1736 | h1736
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1737 | h1737
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1738 | h1738
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1739 | h1739
                  · linarith only [h1587, h1591, h1736, h1739, hc12, hc23, hlam, hphi]
                  · linarith only [h1096, h1584, h1739, hlam]
                · linarith only [h1584, h1738, h672, hlam]
              · linarith only [h1584, h1587, h1591, h1736, h1737, h672, hc12, hc35, hlam, hphi, ht23]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1744 | h1744
              · linarith only [h1096, h1736, h1744, hc03, hc34, hlam, hphi]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1746 | h1746
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1747 | h1747
                  · rcases h2bigk with h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1744, h1747, h2, hc12, hc34, hlam, hphi, ht23, p1748_1]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h2, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h672, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h951, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h0, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1585, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1587, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1589, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1744, h1747, hc02, hc34, hlam, hphi, ht23, p1748_1]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1744, h1747, hc12, hc34, hlam, hphi, ht23, p1748_1]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1736, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1744, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      rcases p1748_3 (m.d 0 2) (by simp) with h1764 | h1764
                      · linarith only [h1764, hlam, p1748_0]
                      · rcases p1748_3 (m.d 1 2) (by simp) with h1766 | h1766
                        · linarith only [h1587, h1766, hlam]
                        · rcases p1748_3 (m.d 2 3) (by simp) with h1768 | h1768
                          · linarith only [h1736, h1768, hlam]
                          · linarith only [h1768, h2, hlam]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      rcases p1748_3 (m.d 0 2) (by simp) with h1771 | h1771
                      · linarith only [h1771, h672, hlam]
                      · linarith only [h0, h1771, hlam]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h0, h2, hc12, hc24, hlam, hphi, p1748_1]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h0, h1736, h951, hc12, hc34, hlam, hphi, ht23, p1748_1]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      rcases p1748_3 (m.d 0 2) (by simp) with h1777 | h1777
                      · linarith only [h1777, hlam, p1748_0]
                      · rcases p1748_3 (m.d 1 2) (by simp) with h1779 | h1779
                        · linarith only [h1589, h1779, hlam]
                        · rcases p1748_3 (m.d 2 3) (by simp) with h1781 | h1781
                          · linarith only [h1744, h1781, hlam]
                          · linarith only [h1781, h2, hlam]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      rcases p1748_3 (m.d 0 2) (by simp) with h1784 | h1784
                      · linarith only [h1784, h951, hlam]
                      · linarith only [h0, h1784, hlam]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h0, h2, hc12, hc25, hlam, hphi, p1748_1]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [h1746, hlam, p1748_0]
                    · have p1748_0 := h1748c.1
                      have p1748_1 := h1748c.2.1
                      have p1748_2 := h1748c.2.2.1
                      have p1748_3 := h1748c.2.2.2
                      linarith only [hlam, p1748_0]
                  · linarith only [h0, h1584, h1736, h1747, h672, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h1584, h1746, h672, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1792 | h1792
    · linarith only [h0, h1792, h2, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1794 | h1794
      · linarith only [h0, h1794, h672, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1796 | h1796
        · linarith only [h0, h1796, h951, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1798 | h1798
          · linarith only [h1, h1584, h1798, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1800 | h1800
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1801 | h1801
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1802 | h1802
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1803 | h1803
                  · linarith only [h0, h1584, h1800, h1803, h672, hc12, hc23, hlam, hphi]
                  · rcases h2bigk with h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h1096, h1802, h1803, h2, hc12, hc24, hlam, hphi, p1805_1]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h2, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h672, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h951, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h0, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h1792, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h1794, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h1796, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      rcases p1805_3 (m.d 0 2) (by simp) with h1816 | h1816
                      · linarith only [h1816, hlam, p1805_0]
                      · rcases p1805_3 (m.d 1 2) (by simp) with h1818 | h1818
                        · linarith only [h1792, h1818, hlam]
                        · rcases p1805_3 (m.d 2 3) (by simp) with h1820 | h1820
                          · rcases p1805_3 (m.d 2 4) (by simp) with h1821 | h1821
                            · linarith only [h1800, h1821, hlam]
                            · linarith only [h1821, h672, hlam]
                          · linarith only [h1820, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      rcases p1805_3 (m.d 0 2) (by simp) with h1825 | h1825
                      · linarith only [h1825, h2, hlam]
                      · linarith only [h0, h1825, hlam]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h1096, h1802, h1803, h2, hc02, hc23, hlam, hphi, p1805_1]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h0, h1096, h1802, h1803, h2, hc12, hc23, hlam, hphi, p1805_1]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      rcases p1805_3 (m.d 0 2) (by simp) with h1831 | h1831
                      · linarith only [h1831, hlam, p1805_0]
                      · rcases p1805_3 (m.d 1 2) (by simp) with h1833 | h1833
                        · linarith only [h1794, h1833, hlam]
                        · rcases p1805_3 (m.d 2 3) (by simp) with h1835 | h1835
                          · rcases p1805_3 (m.d 2 4) (by simp) with h1836 | h1836
                            · rcases p1805_3 (m.d 2 5) (by simp) with h1837 | h1837
                              · linarith only [h1802, h1837, hlam]
                              · linarith only [h1837, h951, hlam]
                            · linarith only [h1836, hlam, p1805_0]
                          · linarith only [h1835, h2, hlam]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      rcases p1805_3 (m.d 0 2) (by simp) with h1842 | h1842
                      · linarith only [h1842, h672, hlam]
                      · linarith only [h0, h1842, hlam]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h1800, hlam, p1805_1]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h0, h1096, h1802, h1803, h2, hc12, hc24, hlam, hphi, p1805_1]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      rcases p1805_3 (m.d 0 2) (by simp) with h1848 | h1848
                      · linarith only [h1848, hlam, p1805_0]
                      · rcases p1805_3 (m.d 1 2) (by simp) with h1850 | h1850
                        · linarith only [h1796, h1850, hlam]
                        · rcases p1805_3 (m.d 2 3) (by simp) with h1852 | h1852
                          · rcases p1805_3 (m.d 2 4) (by simp) with h1853 | h1853
                            · rcases p1805_3 (m.d 2 5) (by simp) with h1854 | h1854
                              · rcases h5bigk with h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p1855_1, u0elo4]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h951, hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1096, hlam, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1584, hlam, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1, hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1796, hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1, h1096, hc05, hlam, hphi, ht0b, ht5b, p1855_1, u0elo0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1798, hlam, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h0, h951, hc12, hc25, hlam, hphi, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1796, hc12, hc25, hlam, hphi, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h0, h1096, h1801, h2, hc12, hc23, hlam, hphi, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1800, h1802, h1803, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h0, h1096, h2, hc12, hc35, hlam, hphi, ht23, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1794, h1798, hc12, hc35, hlam, hphi, ht23, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1801, hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1803, hlam, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h0, h1096, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1794, h1798, hc12, hc45, hlam, hphi, ht23, ht34, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h1802, hlam, p1855_0]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [h0, h1096, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1855_1]
                                · have p1855_0 := h1855c.1
                                  have p1855_1 := h1855c.2.1
                                  have p1855_2 := h1855c.2.2.1
                                  have p1855_3 := h1855c.2.2.2
                                  linarith only [hlam, p1855_0]
                              · linarith only [h1854, hlam, p1805_0]
                            · linarith only [h1853, h672, hlam]
                          · linarith only [h1852, h2, hlam]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      rcases p1805_3 (m.d 0 2) (by simp) with h1884 | h1884
                      · linarith only [h1884, h951, hlam]
                      · linarith only [h0, h1884, hlam]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h1801, hlam, p1805_1]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [h1802, hlam, p1805_0]
                    · have p1805_0 := h1805c.1
                      have p1805_1 := h1805c.2.1
                      have p1805_2 := h1805c.2.2.1
                      have p1805_3 := h1805c.2.2.2
                      linarith only [hlam, p1805_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1890 | h1890
                  · linarith only [h0, h1802, h1890, h672, hc12, hc34, hlam, hphi, ht23]
                  · rcases h2bigk with h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h672, hc12, hc24, hlam, hphi, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h2, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h672, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h951, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h0, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1792, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1794, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1796, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      rcases p1892_3 (m.d 0 2) (by simp) with h1903 | h1903
                      · linarith only [h1903, hlam, p1892_0]
                      · rcases p1892_3 (m.d 1 2) (by simp) with h1905 | h1905
                        · linarith only [h1792, h1905, hlam]
                        · rcases p1892_3 (m.d 2 3) (by simp) with h1907 | h1907
                          · rcases p1892_3 (m.d 2 4) (by simp) with h1908 | h1908
                            · linarith only [h1800, h1908, hlam]
                            · linarith only [h1908, h672, hlam]
                          · linarith only [h1907, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      rcases p1892_3 (m.d 0 2) (by simp) with h1912 | h1912
                      · linarith only [h1912, h2, hlam]
                      · linarith only [h0, h1912, hlam]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h672, hc02, hc23, hlam, hphi, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h0, h951, hc12, hc23, hlam, hphi, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h0, h1802, hc12, hc45, hlam, hphi, ht23, ht34, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1802, hc12, hc45, hlam, hphi, ht23, ht34, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1800, hlam, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1802, hlam, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      rcases p1892_3 (m.d 0 2) (by simp) with h1923 | h1923
                      · linarith only [h1923, hlam, p1892_0]
                      · rcases p1892_3 (m.d 1 2) (by simp) with h1925 | h1925
                        · linarith only [h1796, h1925, hlam]
                        · rcases p1892_3 (m.d 2 3) (by simp) with h1927 | h1927
                          · rcases p1892_3 (m.d 2 4) (by simp) with h1928 | h1928
                            · linarith only [h1802, h1928, hlam]
                            · linarith only [h1928, h672, hlam]
                          · linarith only [h1927, h2, hlam]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      rcases p1892_3 (m.d 0 2) (by simp) with h1932 | h1932
                      · linarith only [h1932, h951, hlam]
                      · linarith only [h0, h1932, hlam]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1801, hlam, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h0, h672, hc12, hc25, hlam, hphi, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1938 | h1938
                · linarith only [h0, h1584, h1800, h1801, h1938, h672, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1940 | h1940
                  · linarith only [h0, h1800, h1801, h1938, h1940, h672, hc12, hc35, hlam, hphi, ht23]
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
                      linarith only [h1800, h672, hc12, hc23, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h2, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h672, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h951, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h0, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1792, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1794, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1796, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1801, h1940, hc02, hc45, hlam, hphi, ht23, ht34, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1801, h1940, hc12, hc45, hlam, hphi, ht23, ht34, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1801, h1940, hc24, hc45, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1801, hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h0, h1800, h1801, h1940, hc12, hc45, hlam, hphi, ht23, ht34, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1800, h1801, h1940, hc12, hc45, hlam, hphi, ht23, ht34, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1800, hlam, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1938, hlam, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      rcases p1942_3 (m.d 0 2) (by simp) with h1963 | h1963
                      · linarith only [h1963, hlam, p1942_0]
                      · rcases p1942_3 (m.d 1 2) (by simp) with h1965 | h1965
                        · linarith only [h1796, h1965, hlam]
                        · rcases p1942_3 (m.d 2 3) (by simp) with h1967 | h1967
                          · linarith only [h1801, h1967, hlam]
                          · linarith only [h1967, h2, hlam]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      rcases p1942_3 (m.d 0 2) (by simp) with h1970 | h1970
                      · linarith only [h1970, h951, hlam]
                      · linarith only [h0, h1970, hlam]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h1800, h1801, h1940, hc34, hc45, hlam, hphi, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [h0, h1801, h1940, h672, hc12, hc45, hlam, hphi, ht23, ht34, p1942_1]
                    · have p1942_0 := h1942c.1
                      have p1942_1 := h1942c.2.1
                      have p1942_2 := h1942c.2.2.1
                      have p1942_3 := h1942c.2.2.2
                      linarith only [hlam, p1942_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1976 | h1976
              · linarith only [h1096, h1800, h1976, hc03, hc34, hlam, hphi]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1978 | h1978
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1979 | h1979
                  · rcases h2bigk with h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1584, h672, hc12, hc45, hlam, hphi, ht23, ht34, p1980_1]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h2, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h672, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h951, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h0, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1792, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1794, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1796, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1976, h1979, hc02, hc34, hlam, hphi, ht23, p1980_1]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1976, h1979, hc12, hc34, hlam, hphi, ht23, p1980_1]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1800, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1976, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      rcases p1980_3 (m.d 0 2) (by simp) with h1996 | h1996
                      · linarith only [h1996, hlam, p1980_0]
                      · rcases p1980_3 (m.d 1 2) (by simp) with h1998 | h1998
                        · linarith only [h1794, h1998, hlam]
                        · rcases p1980_3 (m.d 2 3) (by simp) with h2000 | h2000
                          · linarith only [h1800, h2000, hlam]
                          · linarith only [h2, h2000, hlam]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      rcases p1980_3 (m.d 0 2) (by simp) with h2003 | h2003
                      · linarith only [h2003, h672, hlam]
                      · linarith only [h0, h2003, hlam]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h0, h1800, h2, hc12, hc34, hlam, hphi, ht23, p1980_1]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h0, h1800, h951, hc12, hc34, hlam, hphi, ht23, p1980_1]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      rcases p1980_3 (m.d 0 2) (by simp) with h2009 | h2009
                      · linarith only [h2009, hlam, p1980_0]
                      · rcases p1980_3 (m.d 1 2) (by simp) with h2011 | h2011
                        · linarith only [h1796, h2011, hlam]
                        · rcases p1980_3 (m.d 2 3) (by simp) with h2013 | h2013
                          · linarith only [h1976, h2013, hlam]
                          · linarith only [h2, h2013, hlam]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      rcases p1980_3 (m.d 0 2) (by simp) with h2016 | h2016
                      · linarith only [h2016, h951, hlam]
                      · linarith only [h0, h2016, hlam]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h0, h2, hc12, hc25, hlam, hphi, p1980_1]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [h1978, hlam, p1980_0]
                    · have p1980_0 := h1980c.1
                      have p1980_1 := h1980c.2.1
                      have p1980_2 := h1980c.2.2.1
                      have p1980_3 := h1980c.2.2.2
                      linarith only [hlam, p1980_0]
                  · linarith only [h1800, h1978, h1979, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2023 | h2023
                  · linarith only [h0, h1800, h1978, h2, h2023, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h1800, h2, h2023, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h672 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h951 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h1096 | h1096
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1_x1_x0 m hb0 hb2 hb5 hg0 h1 h2 h672 h951 h1096
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1_x1_x1 m hb0 hb2 hb5 hg0 h1 h2 h672 h951 h1096

set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h672 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h951 | h951
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1_x0 m hb0 hb2 hb5 hg0 h1 h2 h672 h951
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1_x1 m hb0 hb2 hb5 hg0 h1 h2 h672 h951

set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h672 | h672
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x0 m hb0 hb2 hb5 hg0 h1 h2 h672
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1 m hb0 hb2 hb5 hg0 h1 h2 h672

set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x0 m hb0 hb2 hb5 hg0 h1 h2
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1 m hb0 hb2 hb5 hg0 h1 h2

end R2N4
