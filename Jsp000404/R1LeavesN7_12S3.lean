import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h1572 | h1572
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1573 | h1573
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1574 | h1574
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1575 | h1575
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1576 | h1576
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1577 | h1577
            · linarith only [h1577, h2, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1579 | h1579
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1580 | h1580
                · linarith only [h0, h1572, h1580, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h1, h1576, h1579, h1580, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1583 | h1583
                · linarith only [h1575, h1579, h1583, h2, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1585 | h1585
                  · linarith only [h0, h1572, h1575, h1579, h1585, h8, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1587 | h1587
                    · linarith only [h1575, h1587, h2, h8, hlam]
                    · rcases h1bigk with h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1572, h1576, h1579, h1587, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1576, h1579, h1587, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        rcases p1589_3 (m.d 0 1) (by simp) with h1593 | h1593
                        · rcases p1589_3 (m.d 1 2) (by simp) with h1594 | h1594
                          · linarith only [h0, h1594, hlam]
                          · linarith only [h1573, h1594, hlam]
                        · linarith only [h1593, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        rcases p1589_3 (m.d 0 1) (by simp) with h1598 | h1598
                        · rcases p1589_3 (m.d 1 2) (by simp) with h1599 | h1599
                          · linarith only [h0, h1599, hlam]
                          · linarith only [h1574, h1599, hlam]
                        · linarith only [h1598, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h0, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1576, h1579, h1587, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h0, h1575, h1579, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1589_1, u5ehi1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1572, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1, h1575, h1579, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h0, h1572, hc01, hlam, hphi, ht0b, ht5b, p1589_1, u5ehi1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h2, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1573, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1575, hlam, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1577, hlam, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h3, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1574, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1576, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1575, h1579, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1623 | h1623
            · linarith only [h1623, h2, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1625 | h1625
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1626 | h1626
                · linarith only [h0, h1572, h1576, h1626, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1628 | h1628
                  · linarith only [h1628, h5, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1630 | h1630
                    · linarith only [h1574, h1625, h1626, h1630, h8, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h1bigk with h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1574, hc01, hlam, hphi, ht0b, ht5b, p1632_1, u5ehi2]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1635 | h1635
                        · rcases p1632_3 (m.d 1 2) (by simp) with h1636 | h1636
                          · linarith only [h0, h1636, hlam]
                          · linarith only [h1572, h1636, hlam]
                        · linarith only [h1635, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1640 | h1640
                        · rcases p1632_3 (m.d 1 2) (by simp) with h1641 | h1641
                          · linarith only [h0, h1641, hlam]
                          · linarith only [h1573, h1641, hlam]
                        · linarith only [h1640, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1645 | h1645
                        · rcases p1632_3 (m.d 1 2) (by simp) with h1646 | h1646
                          · linarith only [h0, h1646, hlam]
                          · linarith only [h1574, h1646, hlam]
                        · linarith only [h1645, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h0, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h0, h1572, h1625, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1653 | h1653
                        · rcases p1632_3 (m.d 1 2) (by simp) with h1654 | h1654
                          · rcases p1632_3 (m.d 1 3) (by simp) with h1655 | h1655
                            · linarith only [h1572, h1655, hlam]
                            · linarith only [h1575, h1655, hlam]
                          · linarith only [h1573, h1654, hlam]
                        · linarith only [h1653, h2, hlam]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h0, h1572, h1576, h1625, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1572, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1576, h1630, hc14, hc45, hlam, hphi, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1576, hlam, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h2, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1573, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1575, hlam, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1623, hlam, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h3, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1574, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1572, h1625, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1674 | h1674
                        · rcases p1632_3 (m.d 1 2) (by simp) with h1675 | h1675
                          · rcases p1632_3 (m.d 1 3) (by simp) with h1676 | h1676
                            · linarith only [h1576, h1676, hlam]
                            · linarith only [h1575, h1676, hlam]
                          · linarith only [h1573, h1675, hlam]
                        · linarith only [h1674, h2, hlam]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
              · linarith only [h1575, h1576, h1625, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1683 | h1683
          · linarith only [h1575, h1683, h7, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1685 | h1685
            · linarith only [h1575, h1685, h2, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1687 | h1687
              · linarith only [h1572, h1575, h1687, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1689 | h1689
                · linarith only [h0, h1572, h1575, h1683, h1689, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1691 | h1691
                  · linarith only [h0, h1575, h1691, h5, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1693 | h1693
                    · linarith only [h1693, h7, h8, hlam]
                    · rcases h1bigk with h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c | h1695c
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1574, hc01, hlam, hphi, ht0b, ht5b, p1695_1, u5ehi2]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        rcases p1695_3 (m.d 0 1) (by simp) with h1698 | h1698
                        · rcases p1695_3 (m.d 1 2) (by simp) with h1699 | h1699
                          · linarith only [h0, h1699, hlam]
                          · linarith only [h1572, h1699, hlam]
                        · linarith only [h1698, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        rcases p1695_3 (m.d 0 1) (by simp) with h1703 | h1703
                        · rcases p1695_3 (m.d 1 2) (by simp) with h1704 | h1704
                          · linarith only [h0, h1704, hlam]
                          · linarith only [h1573, h1704, hlam]
                        · linarith only [h1703, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        rcases p1695_3 (m.d 0 1) (by simp) with h1708 | h1708
                        · rcases p1695_3 (m.d 1 2) (by simp) with h1709 | h1709
                          · linarith only [h0, h1709, hlam]
                          · linarith only [h1574, h1709, hlam]
                        · linarith only [h1708, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h0, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        rcases p1695_3 (m.d 0 1) (by simp) with h1715 | h1715
                        · rcases p1695_3 (m.d 1 2) (by simp) with h1716 | h1716
                          · rcases p1695_3 (m.d 1 3) (by simp) with h1717 | h1717
                            · linarith only [h1572, h1717, hlam]
                            · rcases p1695_3 (m.d 1 4) (by simp) with h1719 | h1719
                              · linarith only [h1573, h1719, hlam]
                              · linarith only [h1575, h1719, hlam]
                          · linarith only [h1572, h1716, hlam]
                        · linarith only [h1, h1715, hlam]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        rcases p1695_3 (m.d 0 1) (by simp) with h1724 | h1724
                        · rcases p1695_3 (m.d 1 2) (by simp) with h1725 | h1725
                          · rcases p1695_3 (m.d 1 3) (by simp) with h1726 | h1726
                            · linarith only [h1572, h1726, hlam]
                            · rcases p1695_3 (m.d 1 4) (by simp) with h1728 | h1728
                              · linarith only [h1573, h1728, hlam]
                              · rcases p1695_3 (m.d 1 5) (by simp) with h1730 | h1730
                                · linarith only [h1574, h1730, hlam]
                                · linarith only [h1685, h1730, hlam]
                          · linarith only [h1573, h1725, hlam]
                        · linarith only [h1724, h2, hlam]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h0, h1574, hc01, hlam, hphi, ht0b, ht5b, p1695_1, u5ehi2]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1572, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1575, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1683, hlam, p1695_1]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h2, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1573, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1572, h2, h8, hc23, hc45, hlam, hphi, ht34, p1695_1]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1685, hlam, p1695_1]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h3, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [h1574, hlam, p1695_0]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        rcases p1695_3 (m.d 0 1) (by simp) with h1748 | h1748
                        · rcases p1695_3 (m.d 1 2) (by simp) with h1749 | h1749
                          · rcases p1695_3 (m.d 1 3) (by simp) with h1750 | h1750
                            · linarith only [h1683, h1750, hlam]
                            · rcases p1695_3 (m.d 1 4) (by simp) with h1752 | h1752
                              · linarith only [h1685, h1752, hlam]
                              · linarith only [h1575, h1752, hlam]
                          · linarith only [h1572, h1749, hlam]
                        · linarith only [h1, h1748, hlam]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        rcases p1695_3 (m.d 0 1) (by simp) with h1757 | h1757
                        · rcases p1695_3 (m.d 1 2) (by simp) with h1758 | h1758
                          · rcases p1695_3 (m.d 1 3) (by simp) with h1759 | h1759
                            · linarith only [h1683, h1759, hlam]
                            · rcases p1695_3 (m.d 1 4) (by simp) with h1761 | h1761
                              · linarith only [h1685, h1761, hlam]
                              · rcases p1695_3 (m.d 1 5) (by simp) with h1763 | h1763
                                · rcases h2bigk with h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h0, h1572, h1574, h1575, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1695_1, p1764_1]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    rcases p1764_3 (m.d 0 2) (by simp) with h1767 | h1767
                                    · rcases p1764_3 (m.d 1 2) (by simp) with h1768 | h1768
                                      · linarith only [h0, h1768, hlam]
                                      · linarith only [h1572, h1768, hlam]
                                    · linarith only [h1767, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    rcases p1764_3 (m.d 0 2) (by simp) with h1772 | h1772
                                    · rcases p1764_3 (m.d 1 2) (by simp) with h1773 | h1773
                                      · linarith only [h0, h1773, hlam]
                                      · linarith only [h1573, h1773, hlam]
                                    · linarith only [h1772, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    rcases p1764_3 (m.d 0 2) (by simp) with h1777 | h1777
                                    · rcases p1764_3 (m.d 1 2) (by simp) with h1778 | h1778
                                      · linarith only [h0, h1778, hlam]
                                      · linarith only [h1574, h1778, hlam]
                                    · linarith only [h1777, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h0, hlam, p1764_1]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    rcases p1764_3 (m.d 0 2) (by simp) with h1784 | h1784
                                    · rcases p1764_3 (m.d 1 2) (by simp) with h1785 | h1785
                                      · rcases p1764_3 (m.d 2 3) (by simp) with h1786 | h1786
                                        · linarith only [h1786, hlam, p1764_0]
                                        · rcases p1764_3 (m.d 2 4) (by simp) with h1788 | h1788
                                          · linarith only [h1573, h1788, hlam]
                                          · linarith only [h1687, h1788, hlam]
                                      · linarith only [h1785, hlam, p1764_0]
                                    · linarith only [h1784, h4, hlam]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    rcases p1764_3 (m.d 0 2) (by simp) with h1793 | h1793
                                    · rcases p1764_3 (m.d 1 2) (by simp) with h1794 | h1794
                                      · rcases p1764_3 (m.d 2 3) (by simp) with h1795 | h1795
                                        · linarith only [h1572, h1795, hlam]
                                        · rcases p1764_3 (m.d 2 4) (by simp) with h1797 | h1797
                                          · linarith only [h1797, hlam, p1764_0]
                                          · rcases p1764_3 (m.d 2 5) (by simp) with h1799 | h1799
                                            · linarith only [h1574, h1799, hlam]
                                            · linarith only [h1691, h1799, hlam]
                                      · linarith only [h1794, hlam, p1764_0]
                                    · linarith only [h1793, h5, hlam]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1764_1, u5ehi2]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h4, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h1572, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h1687, hlam, p1764_1]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h1689, hlam, p1764_1]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h5, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h1573, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h1573, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1695_1, p1764_1]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h1691, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h6, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h1574, hlam, p1764_0]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h0, h1574, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1764_1]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [h0, h1574, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1764_1]
                                  · have p1764_0 := h1764c.1
                                    have p1764_1 := h1764c.2.1
                                    have p1764_2 := h1764c.2.2.1
                                    have p1764_3 := h1764c.2.2.2
                                    linarith only [hlam, p1764_0]
                                · linarith only [h1685, h1763, hlam]
                          · linarith only [h1573, h1758, hlam]
                        · linarith only [h1757, h2, hlam]
                      · have p1695_0 := h1695c.1
                        have p1695_1 := h1695c.2.1
                        have p1695_2 := h1695c.2.2.1
                        have p1695_3 := h1695c.2.2.2
                        linarith only [hlam, p1695_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1824 | h1824
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1825 | h1825
          · linarith only [h0, h1572, h1574, h1825, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1827 | h1827
            · linarith only [h1827, h2, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1829 | h1829
              · linarith only [h0, h1572, h1574, h1829, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1572, h1574, h1824, h1829, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1832 | h1832
          · linarith only [h1824, h1832, h7, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1834 | h1834
            · linarith only [h0, h1573, h1574, h1834, h6, h8, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1836 | h1836
              · linarith only [h1572, h1824, h1836, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1838 | h1838
                · linarith only [h0, h1572, h1824, h1832, h1838, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1840 | h1840
                  · linarith only [h0, h1573, h1574, h1840, h6, h8, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1842 | h1842
                    · linarith only [h1573, h1574, h1842, h4, h6, h7, h8, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 1) (by simp) with h1846 | h1846
                        · rcases p1844_3 (m.d 1 2) (by simp) with h1847 | h1847
                          · linarith only [h1847, hlam, p1844_0]
                          · rcases p1844_3 (m.d 1 3) (by simp) with h1849 | h1849
                            · linarith only [h1, h1849, hlam]
                            · rcases p1844_3 (m.d 1 4) (by simp) with h1851 | h1851
                              · linarith only [h1851, h2, hlam]
                              · rcases p1844_3 (m.d 1 5) (by simp) with h1853 | h1853
                                · linarith only [h1853, h3, hlam]
                                · linarith only [h1574, h1853, hlam]
                        · linarith only [h1846, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 1) (by simp) with h1857 | h1857
                        · rcases p1844_3 (m.d 1 2) (by simp) with h1858 | h1858
                          · linarith only [h0, h1858, hlam]
                          · linarith only [h1572, h1858, hlam]
                        · linarith only [h1857, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 1) (by simp) with h1862 | h1862
                        · rcases p1844_3 (m.d 1 2) (by simp) with h1863 | h1863
                          · linarith only [h0, h1863, hlam]
                          · linarith only [h1573, h1863, hlam]
                        · linarith only [h1862, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 1) (by simp) with h1867 | h1867
                        · rcases p1844_3 (m.d 1 2) (by simp) with h1868 | h1868
                          · linarith only [h0, h1868, hlam]
                          · rcases p1844_3 (m.d 1 3) (by simp) with h1870 | h1870
                            · linarith only [h1, h1870, hlam]
                            · rcases p1844_3 (m.d 1 4) (by simp) with h1872 | h1872
                              · linarith only [h1872, h2, hlam]
                              · rcases p1844_3 (m.d 1 5) (by simp) with h1874 | h1874
                                · linarith only [h1874, hlam, p1844_0]
                                · rcases h2bigk with h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    rcases p1876_3 (m.d 0 2) (by simp) with h1878 | h1878
                                    · rcases p1876_3 (m.d 1 2) (by simp) with h1879 | h1879
                                      · linarith only [h0, h1879, hlam]
                                      · rcases p1876_3 (m.d 2 3) (by simp) with h1881 | h1881
                                        · linarith only [h1881, h4, hlam]
                                        · rcases p1876_3 (m.d 2 4) (by simp) with h1883 | h1883
                                          · linarith only [h1883, h5, hlam]
                                          · rcases p1876_3 (m.d 2 5) (by simp) with h1885 | h1885
                                            · linarith only [h1885, h6, hlam]
                                            · linarith only [h1574, h1885, hlam]
                                    · linarith only [h0, h1878, hlam]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1573, h1574, h1836, h6, hlam, p1876_2]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1573, h1574, h6, hlam, p1876_2]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1573, h1574, h1836, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1876_1]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h0, hlam, p1876_1]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1574, h1838, hc23, hc35, hlam, hphi, p1876_1]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1574, h1836, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1844_1, p1876_1]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1574, hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h4, hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1572, hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1836, hlam, p1876_1]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1838, hlam, p1876_1]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h5, hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1573, hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h5, h8, hc23, hc45, hlam, hphi, ht34, p1876_1]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h1840, hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h6, hlam, p1876_0]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [h0, h1573, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1876_1]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    rcases p1876_3 (m.d 0 2) (by simp) with h1909 | h1909
                                    · rcases p1876_3 (m.d 1 2) (by simp) with h1910 | h1910
                                      · linarith only [h1574, h1910, hlam]
                                      · linarith only [h1572, h1910, hlam]
                                    · linarith only [h1909, h4, hlam]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    rcases p1876_3 (m.d 0 2) (by simp) with h1914 | h1914
                                    · rcases p1876_3 (m.d 1 2) (by simp) with h1915 | h1915
                                      · linarith only [h1574, h1915, hlam]
                                      · linarith only [h1573, h1915, hlam]
                                    · linarith only [h1914, h5, hlam]
                                  · have p1876_0 := h1876c.1
                                    have p1876_1 := h1876c.2.1
                                    have p1876_2 := h1876c.2.2.1
                                    have p1876_3 := h1876c.2.2.2
                                    linarith only [hlam, p1876_0]
                        · linarith only [h1867, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h0, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h0, h1572, h1574, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h0, h1573, h1574, h1836, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1574, hlam, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1572, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1824, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1832, hlam, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h2, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1573, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1572, h2, h8, hc23, hc45, hlam, hphi, ht34, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1834, hlam, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h3, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1572, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 1) (by simp) with h1938 | h1938
                        · rcases p1844_3 (m.d 1 2) (by simp) with h1939 | h1939
                          · linarith only [h1574, h1939, hlam]
                          · linarith only [h1572, h1939, hlam]
                        · linarith only [h1, h1938, hlam]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 1) (by simp) with h1943 | h1943
                        · rcases p1844_3 (m.d 1 2) (by simp) with h1944 | h1944
                          · linarith only [h1574, h1944, hlam]
                          · linarith only [h1573, h1944, hlam]
                        · linarith only [h1943, h2, hlam]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
    · linarith only [h1572, h1573, h5, h8, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1950 | h1950
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1951 | h1951
      · linarith only [h0, h1572, h1951, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1953 | h1953
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1954 | h1954
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1955 | h1955
            · linarith only [h1955, h2, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1957 | h1957
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1958 | h1958
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1959 | h1959
                  · linarith only [h1950, h1951, h1959, h6, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1961 | h1961
                    · linarith only [h1950, h1951, h1957, h1961, h6, h8, hlam]
                    · rcases h1bigk with h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        rcases p1963_3 (m.d 0 1) (by simp) with h1965 | h1965
                        · rcases p1963_3 (m.d 1 2) (by simp) with h1966 | h1966
                          · linarith only [h1966, hlam, p1963_0]
                          · rcases p1963_3 (m.d 1 3) (by simp) with h1968 | h1968
                            · linarith only [h1, h1968, hlam]
                            · linarith only [h1572, h1968, hlam]
                        · linarith only [h1965, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1954, hc01, hlam, hphi, ht0b, ht5b, p1963_1, u5ehi3]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        rcases p1963_3 (m.d 0 1) (by simp) with h1973 | h1973
                        · rcases p1963_3 (m.d 1 2) (by simp) with h1974 | h1974
                          · linarith only [h0, h1974, hlam]
                          · linarith only [h1950, h1974, hlam]
                        · linarith only [h1973, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        rcases p1963_3 (m.d 0 1) (by simp) with h1978 | h1978
                        · rcases p1963_3 (m.d 1 2) (by simp) with h1979 | h1979
                          · linarith only [h0, h1979, hlam]
                          · rcases p1963_3 (m.d 1 3) (by simp) with h1981 | h1981
                            · linarith only [h1, h1981, hlam]
                            · linarith only [h1954, h1981, hlam]
                        · linarith only [h1978, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h0, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1572, hlam, p1963_1]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h0, h1951, h1958, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1963_1]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1951, hlam, p1963_1]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1, h1950, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1963_1]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        rcases p1963_3 (m.d 0 1) (by simp) with h1993 | h1993
                        · rcases p1963_3 (m.d 1 2) (by simp) with h1994 | h1994
                          · linarith only [h1572, h1994, hlam]
                          · linarith only [h1950, h1994, hlam]
                        · linarith only [h1993, h2, hlam]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h0, h1572, h1950, h1951, h1957, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1963_1]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h2, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1950, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1953, hlam, p1963_1]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1955, hlam, p1963_1]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h3, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1950, h1957, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1963_1]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [h1954, hlam, p1963_0]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        rcases p1963_3 (m.d 0 1) (by simp) with h2007 | h2007
                        · rcases p1963_3 (m.d 1 2) (by simp) with h2008 | h2008
                          · linarith only [h1951, h2008, hlam]
                          · linarith only [h1950, h2008, hlam]
                        · linarith only [h2, h2007, hlam]
                      · have p1963_0 := h1963c.1
                        have p1963_1 := h1963c.2.1
                        have p1963_2 := h1963c.2.2.1
                        have p1963_3 := h1963c.2.2.2
                        linarith only [hlam, p1963_0]
                · linarith only [h1572, h1954, h1958, hlam]
              · linarith only [h0, h1572, h1954, h1957, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2015 | h2015
            · linarith only [h2, h2015, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2017 | h2017
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2018 | h2018
                · linarith only [h0, h1572, h1950, h1954, h2017, h2018, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2020 | h2020
                  · linarith only [h1572, h1950, h2018, h2020, h6, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2022 | h2022
                    · linarith only [h1572, h1950, h2017, h2018, h2022, h6, h8, hlam]
                    · linarith only [h1572, h1950, h2017, h2018, h2022, hc34, hc45, hlam, hphi]
              · linarith only [h0, h1572, h1950, h2017, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1572, h1950, h1953, h7, h8, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2027 | h2027
      · linarith only [h1950, h2027, h5, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2029 | h2029
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2030 | h2030
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2031 | h2031
            · linarith only [h1950, h2, h2031, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2033 | h2033
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2034 | h2034
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2035 | h2035
                  · linarith only [h2035, h5, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2037 | h2037
                    · linarith only [h1950, h2037, h5, h8, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2041 | h2041
                        · rcases p2039_3 (m.d 1 2) (by simp) with h2042 | h2042
                          · linarith only [h2042, hlam, p2039_0]
                          · rcases p2039_3 (m.d 1 3) (by simp) with h2044 | h2044
                            · linarith only [h1, h2044, hlam]
                            · linarith only [h1572, h2044, hlam]
                        · linarith only [h2041, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2030, hc01, hlam, hphi, ht0b, ht5b, p2039_1, u5ehi3]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2049 | h2049
                        · rcases p2039_3 (m.d 1 2) (by simp) with h2050 | h2050
                          · linarith only [h0, h2050, hlam]
                          · rcases p2039_3 (m.d 1 3) (by simp) with h2052 | h2052
                            · linarith only [h1, h2052, hlam]
                            · linarith only [h2029, h2052, hlam]
                        · linarith only [h2049, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2056 | h2056
                        · rcases p2039_3 (m.d 1 2) (by simp) with h2057 | h2057
                          · linarith only [h0, h2057, hlam]
                          · rcases p2039_3 (m.d 1 3) (by simp) with h2059 | h2059
                            · linarith only [h1, h2059, hlam]
                            · linarith only [h2030, h2059, hlam]
                        · linarith only [h2056, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h0, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h1572, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h1950, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2027, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h1, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2069 | h2069
                        · rcases p2039_3 (m.d 1 2) (by simp) with h2070 | h2070
                          · linarith only [h1572, h2070, hlam]
                          · rcases p2039_3 (m.d 1 3) (by simp) with h2072 | h2072
                            · rcases p2039_3 (m.d 1 4) (by simp) with h2073 | h2073
                              · linarith only [h2029, h2073, hlam]
                              · linarith only [h1950, h2073, hlam]
                            · linarith only [h1572, h2072, hlam]
                        · linarith only [h0, h2069, hlam]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2079 | h2079
                        · rcases p2039_3 (m.d 1 2) (by simp) with h2080 | h2080
                          · linarith only [h1572, h2080, hlam]
                          · rcases p2039_3 (m.d 1 3) (by simp) with h2082 | h2082
                            · rcases p2039_3 (m.d 1 4) (by simp) with h2083 | h2083
                              · linarith only [h2029, h2083, hlam]
                              · rcases p2039_3 (m.d 1 5) (by simp) with h2085 | h2085
                                · linarith only [h2030, h2085, hlam]
                                · linarith only [h2031, h2085, hlam]
                            · linarith only [h2029, h2082, hlam]
                        · linarith only [h2, h2079, hlam]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h0, h1572, h2030, h4, hc01, hlam, hphi, ht0b, ht5b, p2039_1, u5ehi3]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2029, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2031, hlam, p2039_1]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h3, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2097 | h2097
                        · rcases p2039_3 (m.d 1 2) (by simp) with h2098 | h2098
                          · linarith only [h2027, h2098, hlam]
                          · rcases p2039_3 (m.d 1 3) (by simp) with h2100 | h2100
                            · rcases p2039_3 (m.d 1 4) (by simp) with h2101 | h2101
                              · linarith only [h2031, h2101, hlam]
                              · linarith only [h1950, h2101, hlam]
                            · linarith only [h1572, h2100, hlam]
                        · linarith only [h0, h2097, hlam]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [h2030, hlam, p2039_0]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        rcases p2039_3 (m.d 0 1) (by simp) with h2107 | h2107
                        · rcases p2039_3 (m.d 1 2) (by simp) with h2108 | h2108
                          · linarith only [h2027, h2108, hlam]
                          · rcases p2039_3 (m.d 1 3) (by simp) with h2110 | h2110
                            · rcases p2039_3 (m.d 1 4) (by simp) with h2111 | h2111
                              · linarith only [h2031, h2111, hlam]
                              · rcases p2039_3 (m.d 1 5) (by simp) with h2113 | h2113
                                · rcases h2bigk with h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h1950, h2027, h6, hlam, p2039_1, p2114_2]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h1572, h2030, hc02, hlam, hphi, ht0b, ht5b, p2114_1, u5ehi3]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 2) (by simp) with h2118 | h2118
                                    · rcases p2114_3 (m.d 1 2) (by simp) with h2119 | h2119
                                      · linarith only [h0, h2119, hlam]
                                      · rcases p2114_3 (m.d 2 3) (by simp) with h2121 | h2121
                                        · linarith only [h2121, h4, hlam]
                                        · linarith only [h2033, h2121, hlam]
                                    · linarith only [h2118, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h0, h1950, h2027, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2039_1, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h0, hlam, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h1572, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h1950, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2027, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h4, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 2) (by simp) with h2132 | h2132
                                    · rcases p2114_3 (m.d 1 2) (by simp) with h2133 | h2133
                                      · linarith only [h2133, hlam, p2114_0]
                                      · rcases p2114_3 (m.d 2 3) (by simp) with h2135 | h2135
                                        · rcases p2114_3 (m.d 2 4) (by simp) with h2136 | h2136
                                          · linarith only [h2033, h2136, hlam]
                                          · linarith only [h1950, h2136, hlam]
                                        · linarith only [h2135, hlam, p2114_0]
                                    · linarith only [h0, h2132, hlam]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h0, h1950, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h0, h1950, h2027, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2039_1, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h5, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2033, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2035, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h6, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 2) (by simp) with h2150 | h2150
                                    · rcases p2114_3 (m.d 1 2) (by simp) with h2151 | h2151
                                      · linarith only [h2151, hlam, p2114_0]
                                      · rcases p2114_3 (m.d 2 3) (by simp) with h2153 | h2153
                                        · rcases p2114_3 (m.d 2 4) (by simp) with h2154 | h2154
                                          · linarith only [h2035, h2154, hlam]
                                          · linarith only [h1950, h2154, hlam]
                                        · linarith only [h1572, h2153, hlam]
                                    · linarith only [h0, h2150, hlam]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2034, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h1950, hc12, hc25, hlam, hphi, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                · linarith only [h2031, h2113, hlam]
                            · linarith only [h2029, h2110, hlam]
                        · linarith only [h2, h2107, hlam]
                      · have p2039_0 := h2039c.1
                        have p2039_1 := h2039c.2.1
                        have p2039_2 := h2039c.2.2.1
                        have p2039_3 := h2039c.2.2.2
                        linarith only [hlam, p2039_0]
                · linarith only [h1572, h2030, h2034, hlam]
              · linarith only [h1572, h2, h2029, h2030, h2033, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2168 | h2168
            · linarith only [h1950, h2168, h5, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2170 | h2170
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2171 | h2171
                · linarith only [h0, h2029, h2030, h2171, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2173 | h2173
                  · linarith only [h2173, h5, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2175 | h2175
                    · linarith only [h1, h2029, h2175, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        rcases p2177_3 (m.d 0 1) (by simp) with h2179 | h2179
                        · rcases p2177_3 (m.d 1 2) (by simp) with h2180 | h2180
                          · linarith only [h2180, hlam, p2177_0]
                          · rcases p2177_3 (m.d 1 3) (by simp) with h2182 | h2182
                            · linarith only [h1, h2182, hlam]
                            · linarith only [h1572, h2182, hlam]
                        · linarith only [h2179, hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        rcases p2177_3 (m.d 0 1) (by simp) with h2186 | h2186
                        · rcases p2177_3 (m.d 1 2) (by simp) with h2187 | h2187
                          · linarith only [h0, h2187, hlam]
                          · rcases p2177_3 (m.d 1 3) (by simp) with h2189 | h2189
                            · linarith only [h2189, hlam, p2177_0]
                            · rcases p2177_3 (m.d 1 4) (by simp) with h2191 | h2191
                              · linarith only [h2, h2191, hlam]
                              · rcases p2177_3 (m.d 1 5) (by simp) with h2193 | h2193
                                · linarith only [h2193, h3, hlam]
                                · linarith only [h2030, h2193, hlam]
                        · linarith only [h2186, hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        rcases p2177_3 (m.d 0 1) (by simp) with h2197 | h2197
                        · rcases p2177_3 (m.d 1 2) (by simp) with h2198 | h2198
                          · linarith only [h0, h2198, hlam]
                          · rcases p2177_3 (m.d 1 3) (by simp) with h2200 | h2200
                            · linarith only [h1, h2200, hlam]
                            · linarith only [h2029, h2200, hlam]
                        · linarith only [h2197, hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        rcases p2177_3 (m.d 0 1) (by simp) with h2204 | h2204
                        · rcases p2177_3 (m.d 1 2) (by simp) with h2205 | h2205
                          · linarith only [h0, h2205, hlam]
                          · rcases p2177_3 (m.d 1 3) (by simp) with h2207 | h2207
                            · linarith only [h1, h2207, hlam]
                            · rcases p2177_3 (m.d 1 4) (by simp) with h2209 | h2209
                              · linarith only [h2, h2209, hlam]
                              · rcases p2177_3 (m.d 1 5) (by simp) with h2211 | h2211
                                · linarith only [h2211, hlam, p2177_0]
                                · rcases h2bigk with h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c | h2213c
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    rcases p2213_3 (m.d 0 2) (by simp) with h2215 | h2215
                                    · rcases p2213_3 (m.d 1 2) (by simp) with h2216 | h2216
                                      · linarith only [h0, h2216, hlam]
                                      · rcases p2213_3 (m.d 2 3) (by simp) with h2218 | h2218
                                        · linarith only [h2218, h4, hlam]
                                        · linarith only [h1572, h2218, hlam]
                                    · linarith only [h0, h2215, hlam]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    rcases p2213_3 (m.d 0 2) (by simp) with h2222 | h2222
                                    · rcases p2213_3 (m.d 1 2) (by simp) with h2223 | h2223
                                      · linarith only [h0, h2223, hlam]
                                      · rcases p2213_3 (m.d 2 3) (by simp) with h2225 | h2225
                                        · linarith only [h2225, hlam, p2213_0]
                                        · rcases p2213_3 (m.d 2 4) (by simp) with h2227 | h2227
                                          · linarith only [h2227, h5, hlam]
                                          · rcases p2213_3 (m.d 2 5) (by simp) with h2229 | h2229
                                            · linarith only [h2229, h6, hlam]
                                            · linarith only [h2171, h2229, hlam]
                                    · linarith only [h2222, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    rcases p2213_3 (m.d 0 2) (by simp) with h2233 | h2233
                                    · rcases p2213_3 (m.d 1 2) (by simp) with h2234 | h2234
                                      · linarith only [h0, h2234, hlam]
                                      · rcases p2213_3 (m.d 2 3) (by simp) with h2236 | h2236
                                        · linarith only [h2236, h4, hlam]
                                        · linarith only [h2170, h2236, hlam]
                                    · linarith only [h2233, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    rcases p2213_3 (m.d 0 2) (by simp) with h2240 | h2240
                                    · rcases p2213_3 (m.d 1 2) (by simp) with h2241 | h2241
                                      · linarith only [h0, h2241, hlam]
                                      · rcases p2213_3 (m.d 2 3) (by simp) with h2243 | h2243
                                        · linarith only [h2243, h4, hlam]
                                        · rcases p2213_3 (m.d 2 4) (by simp) with h2245 | h2245
                                          · linarith only [h2245, h5, hlam]
                                          · rcases p2213_3 (m.d 2 5) (by simp) with h2247 | h2247
                                            · linarith only [h2247, hlam, p2213_0]
                                            · rcases h4bigk with h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c | h2249c
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h8, hc14, hc45, hlam, hphi, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h1950, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h8, hc34, hc45, hlam, hphi, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h8, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h2, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h1950, hlam, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h2, h8, hc34, hc45, hlam, hphi, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h2168, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h5, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h0, h2170, h2171, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2213_1, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h0, h2170, h2171, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2213_1, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h2173, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h7, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h2029, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h2170, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h2175, hlam, p2249_0]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h1950, h5, hc12, hc45, hlam, hphi, ht23, ht34, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                rcases p2249_3 (m.d 0 4) (by simp) with h2271 | h2271
                                                · linarith only [h2271, h8, hlam]
                                                · linarith only [h2, h2271, hlam]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [h1950, hc12, hc45, hlam, hphi, ht23, ht34, p2249_1]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                rcases p2249_3 (m.d 0 4) (by simp) with h2275 | h2275
                                                · linarith only [h2275, h8, hlam]
                                                · linarith only [h2275, h7, hlam]
                                              · have p2249_0 := h2249c.1
                                                have p2249_1 := h2249c.2.1
                                                have p2249_2 := h2249c.2.2.1
                                                have p2249_3 := h2249c.2.2.2
                                                linarith only [hlam, p2249_0]
                                    · linarith only [h2240, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h0, hlam, p2213_1]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h1572, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h1950, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h2027, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h4, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h2171, hc12, hc35, hlam, hphi, ht23, p2213_1]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h1950, h2171, hc12, hc35, hlam, hphi, ht23, p2213_1]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h2171, hlam, p2213_1]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h5, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2213_1]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h2170, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h2173, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h6, hlam, p2213_0]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    rcases p2213_3 (m.d 0 2) (by simp) with h2296 | h2296
                                    · rcases p2213_3 (m.d 1 2) (by simp) with h2297 | h2297
                                      · linarith only [h2297, hlam, p2213_0]
                                      · rcases p2213_3 (m.d 2 3) (by simp) with h2299 | h2299
                                        · linarith only [h2171, h2299, hlam]
                                        · linarith only [h1572, h2299, hlam]
                                    · linarith only [h0, h2296, hlam]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h0, h1572, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2213_1]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [h0, h1950, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2213_1]
                                  · have p2213_0 := h2213c.1
                                    have p2213_1 := h2213c.2.1
                                    have p2213_2 := h2213c.2.2.1
                                    have p2213_3 := h2213c.2.2.2
                                    linarith only [hlam, p2213_0]
                        · linarith only [h2204, hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h0, hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h1572, hlam, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h1950, hlam, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h2027, hlam, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h1, hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h2030, h2175, hc12, hc45, hlam, hphi, ht23, ht34, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h1950, h2030, h2175, hc12, hc45, hlam, hphi, ht23, ht34, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h2030, hlam, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h2, hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h2029, hlam, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h2168, hlam, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h3, hlam, p2177_0]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        rcases p2177_3 (m.d 0 1) (by simp) with h2323 | h2323
                        · rcases p2177_3 (m.d 1 2) (by simp) with h2324 | h2324
                          · linarith only [h2027, h2324, hlam]
                          · rcases p2177_3 (m.d 1 3) (by simp) with h2326 | h2326
                            · linarith only [h2030, h2326, hlam]
                            · linarith only [h1572, h2326, hlam]
                        · linarith only [h0, h2323, hlam]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [h0, h2027, h2029, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2177_1]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        rcases p2177_3 (m.d 0 1) (by simp) with h2331 | h2331
                        · rcases p2177_3 (m.d 1 2) (by simp) with h2332 | h2332
                          · linarith only [h2027, h2332, hlam]
                          · rcases p2177_3 (m.d 1 3) (by simp) with h2334 | h2334
                            · linarith only [h2030, h2334, hlam]
                            · linarith only [h2029, h2334, hlam]
                        · linarith only [h2, h2331, hlam]
                      · have p2177_0 := h2177c.1
                        have p2177_1 := h2177c.2.1
                        have p2177_2 := h2177c.2.2.1
                        have p2177_3 := h2177c.2.2.2
                        linarith only [hlam, p2177_0]
              · linarith only [h1, h1572, h2029, h2170, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2340 | h2340
          · linarith only [h2029, h2340, h7, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2342 | h2342
            · linarith only [h2, h2029, h2342, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2344 | h2344
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2345 | h2345
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2346 | h2346
                  · linarith only [h2346, h5, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2348 | h2348
                    · linarith only [h2344, h2348, h5, h8, hlam]
                    · rcases h1bigk with h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h1572, h2340, h2345, h4, hlam, p2350_2]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h2340, h2345, h4, hlam, p2350_2]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        rcases p2350_3 (m.d 0 1) (by simp) with h2354 | h2354
                        · rcases p2350_3 (m.d 1 2) (by simp) with h2355 | h2355
                          · linarith only [h0, h2355, hlam]
                          · rcases p2350_3 (m.d 1 3) (by simp) with h2357 | h2357
                            · linarith only [h1, h2357, hlam]
                            · rcases p2350_3 (m.d 1 4) (by simp) with h2359 | h2359
                              · linarith only [h2359, hlam, p2350_0]
                              · rcases p2350_3 (m.d 1 5) (by simp) with h2361 | h2361
                                · linarith only [h2361, h3, hlam]
                                · linarith only [h2342, h2361, hlam]
                        · linarith only [h2354, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        rcases p2350_3 (m.d 0 1) (by simp) with h2365 | h2365
                        · rcases p2350_3 (m.d 1 2) (by simp) with h2366 | h2366
                          · linarith only [h0, h2366, hlam]
                          · rcases p2350_3 (m.d 1 3) (by simp) with h2368 | h2368
                            · linarith only [h1, h2368, hlam]
                            · rcases p2350_3 (m.d 1 4) (by simp) with h2370 | h2370
                              · linarith only [h2, h2370, hlam]
                              · rcases p2350_3 (m.d 1 5) (by simp) with h2372 | h2372
                                · linarith only [h2372, hlam, p2350_0]
                                · rcases h2bigk with h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h1572, h2029, h2345, h2348, h4, hlam, p2374_2]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h0, h1572, h2029, h2345, h2348, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2374_1]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    rcases p2374_3 (m.d 0 2) (by simp) with h2378 | h2378
                                    · rcases p2374_3 (m.d 1 2) (by simp) with h2379 | h2379
                                      · linarith only [h0, h2379, hlam]
                                      · rcases p2374_3 (m.d 2 3) (by simp) with h2381 | h2381
                                        · linarith only [h2381, h4, hlam]
                                        · linarith only [h2344, h2381, hlam]
                                    · linarith only [h2378, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    rcases p2374_3 (m.d 0 2) (by simp) with h2385 | h2385
                                    · rcases p2374_3 (m.d 1 2) (by simp) with h2386 | h2386
                                      · linarith only [h0, h2386, hlam]
                                      · rcases p2374_3 (m.d 2 3) (by simp) with h2388 | h2388
                                        · linarith only [h2388, h4, hlam]
                                        · linarith only [h2345, h2388, hlam]
                                    · linarith only [h2385, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h0, hlam, p2374_1]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h1572, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h1950, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h2027, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h4, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    rcases p2374_3 (m.d 0 2) (by simp) with h2398 | h2398
                                    · rcases p2374_3 (m.d 1 2) (by simp) with h2399 | h2399
                                      · linarith only [h2399, hlam, p2374_0]
                                      · rcases p2374_3 (m.d 2 3) (by simp) with h2401 | h2401
                                        · rcases p2374_3 (m.d 2 4) (by simp) with h2402 | h2402
                                          · linarith only [h2344, h2402, hlam]
                                          · linarith only [h1950, h2402, hlam]
                                        · linarith only [h2401, hlam, p2374_0]
                                    · linarith only [h0, h2398, hlam]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h1572, h2029, h2344, hc12, hc23, hlam, hphi, p2374_1]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p2374_1, u5ehi2]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h5, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2374_1]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h2344, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h2346, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h6, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    rcases p2374_3 (m.d 0 2) (by simp) with h2416 | h2416
                                    · rcases p2374_3 (m.d 1 2) (by simp) with h2417 | h2417
                                      · linarith only [h2417, hlam, p2374_0]
                                      · rcases p2374_3 (m.d 2 3) (by simp) with h2419 | h2419
                                        · rcases p2374_3 (m.d 2 4) (by simp) with h2420 | h2420
                                          · linarith only [h2346, h2420, hlam]
                                          · linarith only [h1950, h2420, hlam]
                                        · linarith only [h1572, h2419, hlam]
                                    · linarith only [h0, h2416, hlam]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h2345, hlam, p2374_0]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [h0, h1950, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2374_1]
                                  · have p2374_0 := h2374c.1
                                    have p2374_1 := h2374c.2.1
                                    have p2374_2 := h2374c.2.2.1
                                    have p2374_3 := h2374c.2.2.2
                                    linarith only [hlam, p2374_0]
                        · linarith only [h2365, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h1572, hlam, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h1950, hlam, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2027, hlam, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h1, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2029, hc12, hc34, hlam, hphi, ht23, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2029, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2340, hlam, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h1950, h5, h8, hc13, hc45, hlam, hphi, ht34, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2342, hlam, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h3, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h2340, h2345, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h1572, h2340, h2345, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h2340, h2345, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                · linarith only [h1572, h2029, h2344, h2345, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1572, h2344, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8

end R2N4
