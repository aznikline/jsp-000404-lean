import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 4 5 (by decide) (by decide) with h1539 | h1539
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1541 | h1541
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1542 | h1542
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1543 | h1543
          · linarith only [h1, h1543, h5, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1545 | h1545
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1546 | h1546
              · linarith only [h1546, h2, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1548 | h1548
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1549 | h1549
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1550 | h1550
                    · rcases h2bigk with h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h0, h1541, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h0, h1548, h1550, hc01, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h0, h1546, h1548, h1550, hc01, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        rcases p1551_3 (m.d 0 2) (by simp) with h1556 | h1556
                        · rcases p1551_3 (m.d 1 2) (by simp) with h1557 | h1557
                          · linarith only [h0, h1557, hlam]
                          · linarith only [h1542, h1557, hlam]
                        · linarith only [h1556, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h0, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h1548, h1550, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h0, h1546, h1548, h1550, hc01, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h2, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h1540, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h1546, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h2, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h3, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h1541, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h1548, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h0, h1541, h1548, h1550, hc01, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h4, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h1542, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h1548, hlam, p1551_1]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [h1549, hlam, p1551_0]
                      · have p1551_0 := h1551c.1
                        have p1551_1 := h1551c.2.1
                        have p1551_2 := h1551c.2.2.1
                        have p1551_3 := h1551c.2.2.2
                        linarith only [hlam, p1551_0]
                    · linarith only [h1539, h1550, h5, hlam]
                  · linarith only [h1, h1545, h1546, h1548, h1549, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1583 | h1583
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1584 | h1584
                    · rcases h2bigk with h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, h1540, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        rcases p1585_3 (m.d 0 2) (by simp) with h1588 | h1588
                        · rcases p1585_3 (m.d 1 2) (by simp) with h1589 | h1589
                          · linarith only [h0, h1589, hlam]
                          · linarith only [h1540, h1589, hlam]
                        · linarith only [h1588, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, h1583, hc01, hc45, hlam, hphi, ht0b, ht5b, p1585_1]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        rcases p1585_3 (m.d 0 2) (by simp) with h1594 | h1594
                        · rcases p1585_3 (m.d 1 2) (by simp) with h1595 | h1595
                          · linarith only [h0, h1595, hlam]
                          · linarith only [h1542, h1595, hlam]
                        · linarith only [h1594, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, h1583, hc01, hc45, hlam, hphi, ht0b, ht5b, p1585_1]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1585_1]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h2, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h1540, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h1546, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h1548, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h3, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h1541, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, h1541, h1548, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h4, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h1542, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1585_1]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [h1583, hlam, p1585_0]
                      · have p1585_0 := h1585c.1
                        have p1585_1 := h1585c.2.1
                        have p1585_2 := h1585c.2.2.1
                        have p1585_3 := h1585c.2.2.2
                        linarith only [hlam, p1585_0]
                    · linarith only [h1539, h1584, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1620 | h1620
                    · rcases h2bigk with h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h0, h1540, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1621_1]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        rcases p1621_3 (m.d 0 2) (by simp) with h1624 | h1624
                        · rcases p1621_3 (m.d 1 2) (by simp) with h1625 | h1625
                          · linarith only [h0, h1625, hlam]
                          · linarith only [h1540, h1625, hlam]
                        · linarith only [h1624, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        rcases p1621_3 (m.d 0 2) (by simp) with h1629 | h1629
                        · rcases p1621_3 (m.d 1 2) (by simp) with h1630 | h1630
                          · linarith only [h0, h1630, hlam]
                          · linarith only [h1541, h1630, hlam]
                        · linarith only [h1629, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        rcases p1621_3 (m.d 0 2) (by simp) with h1634 | h1634
                        · rcases p1621_3 (m.d 1 2) (by simp) with h1635 | h1635
                          · linarith only [h0, h1635, hlam]
                          · linarith only [h1542, h1635, hlam]
                        · linarith only [h1634, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h0, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1621_1]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h0, h1546, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1621_1]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p1621_1]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h2, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h1540, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h1546, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h1548, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h3, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h1541, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h1, h1545, h1583, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1621_1]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h1583, hlam, p1621_1]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h4, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h1542, hlam, p1621_0]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1621_1]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [h0, h1541, h1545, h1583, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1621_1]
                      · have p1621_0 := h1621c.1
                        have p1621_1 := h1621c.2.1
                        have p1621_2 := h1621c.2.2.1
                        have p1621_3 := h1621c.2.2.2
                        linarith only [hlam, p1621_0]
                    · linarith only [h1, h1545, h1620, h5, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1660 | h1660
              · linarith only [h1539, h1540, h1543, h1545, h1660, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1662 | h1662
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1663 | h1663
                  · linarith only [h0, h1540, h1543, h1545, h1662, h1663, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1660, h1662, h1663, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1666 | h1666
                  · linarith only [h0, h1541, h1543, h1545, h1666, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1668 | h1668
                    · rcases h2bigk with h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h0, h1540, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        rcases p1669_3 (m.d 0 2) (by simp) with h1672 | h1672
                        · rcases p1669_3 (m.d 1 2) (by simp) with h1673 | h1673
                          · linarith only [h0, h1673, hlam]
                          · linarith only [h1540, h1673, hlam]
                        · linarith only [h1672, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        rcases p1669_3 (m.d 0 2) (by simp) with h1677 | h1677
                        · rcases p1669_3 (m.d 1 2) (by simp) with h1678 | h1678
                          · linarith only [h0, h1678, hlam]
                          · linarith only [h1541, h1678, hlam]
                        · linarith only [h1677, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        rcases p1669_3 (m.d 0 2) (by simp) with h1682 | h1682
                        · rcases p1669_3 (m.d 1 2) (by simp) with h1683 | h1683
                          · linarith only [h0, h1683, hlam]
                          · linarith only [h1542, h1683, hlam]
                        · linarith only [h1682, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h0, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h0, h1660, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h0, h1660, h1666, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h2, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h1540, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h1660, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h1662, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h3, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h1541, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h1666, hlam, p1669_1]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h4, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h1542, hlam, p1669_0]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h1539, h1542, h1545, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [h1539, h1542, h1545, h5, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1669_1]
                      · have p1669_0 := h1669c.1
                        have p1669_1 := h1669c.2.1
                        have p1669_2 := h1669c.2.2.1
                        have p1669_3 := h1669c.2.2.2
                        linarith only [hlam, p1669_0]
                    · linarith only [h1539, h1668, h5, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1708 | h1708
          · linarith only [h1539, h1540, h1542, h1708, h4, h5, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1710 | h1710
            · linarith only [h1541, h1542, h1710, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1712 | h1712
              · linarith only [h1539, h1540, h1708, h1710, h1712, h5, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1714 | h1714
                · linarith only [h0, h1541, h1542, h1712, h1714, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1716 | h1716
                  · linarith only [h1541, h1542, h1710, h1716, hlam]
                  · linarith only [h1539, h1541, h1542, h1712, h1716, h5, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1719 | h1719
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1720 | h1720
          · linarith only [h0, h1540, h1541, h1720, h3, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1722 | h1722
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1723 | h1723
              · linarith only [h1540, h1541, h1723, h3, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                · linarith only [h0, h1540, h1541, h1725, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1727 | h1727
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1728 | h1728
                    · rcases h2bigk with h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h0, h1719, h1725, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1729_1]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        rcases p1729_3 (m.d 0 2) (by simp) with h1732 | h1732
                        · rcases p1729_3 (m.d 1 2) (by simp) with h1733 | h1733
                          · linarith only [h0, h1733, hlam]
                          · linarith only [h1540, h1733, hlam]
                        · linarith only [h1732, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h0, h1541, h1719, h1725, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1729_1]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        rcases p1729_3 (m.d 0 2) (by simp) with h1738 | h1738
                        · rcases p1729_3 (m.d 1 2) (by simp) with h1739 | h1739
                          · linarith only [h0, h1739, hlam]
                          · linarith only [h1719, h1739, hlam]
                        · linarith only [h1738, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h0, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1541, h3, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1729_1]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1541, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1541, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1729_1]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h2, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1540, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1723, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1725, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h3, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p1729_1]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1729_1]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h0, h1725, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1729_1]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h4, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1719, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1719, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1729_1]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [h1727, hlam, p1729_0]
                      · have p1729_0 := h1729c.1
                        have p1729_1 := h1729c.2.1
                        have p1729_2 := h1729c.2.2.1
                        have p1729_3 := h1729c.2.2.2
                        linarith only [hlam, p1729_0]
                    · linarith only [h1539, h1728, h5, hlam]
                  · linarith only [h1541, h1719, h1722, h1727, hlam]
            · linarith only [h1539, h1540, h1541, h1722, h5, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1766 | h1766
          · linarith only [h1, h1540, h1541, h1766, h5, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1768 | h1768
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1769 | h1769
              · linarith only [h1769, h2, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1771 | h1771
                · linarith only [h0, h1540, h1719, h1771, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1773 | h1773
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1774 | h1774
                    · rcases h2bigk with h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c | h1775c
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h0, h1540, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        rcases p1775_3 (m.d 0 2) (by simp) with h1778 | h1778
                        · rcases p1775_3 (m.d 1 2) (by simp) with h1779 | h1779
                          · linarith only [h0, h1779, hlam]
                          · linarith only [h1540, h1779, hlam]
                        · linarith only [h1778, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h0, h1540, h1541, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h0, h1540, h1719, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h0, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h1541, h3, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h1541, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h1719, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h2, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h1540, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h1769, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h1771, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h3, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h0, h1540, h1719, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h4, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h1540, h4, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1775_1]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [h1773, hlam, p1775_0]
                      · have p1775_0 := h1775c.1
                        have p1775_1 := h1775c.2.1
                        have p1775_2 := h1775c.2.2.1
                        have p1775_3 := h1775c.2.2.2
                        linarith only [hlam, p1775_0]
                    · linarith only [h1539, h1774, h5, hlam]
                  · linarith only [h1541, h1768, h1773, hlam]
            · linarith only [h1539, h1540, h1541, h1768, h5, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1808 | h1808
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1809 | h1809
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1810 | h1810
          · linarith only [h1540, h1808, h1810, h2, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h1540, h1808, h1810, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1813 | h1813
          · linarith only [h1540, h1808, h1813, h2, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h1540, h1808, h1813, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1816 | h1816
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1817 | h1817
          · linarith only [h1540, h1816, h1817, h2, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1819 | h1819
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1820 | h1820
              · linarith only [h1820, h2, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1822 | h1822
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1823 | h1823
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1824 | h1824
                    · rcases h2bigk with h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h0, h1816, h1822, h1824, hc01, hc45, hlam, hphi, ht0b, ht5b, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h0, h1540, h1816, h1822, h1824, hc01, hc45, hlam, hphi, ht0b, ht5b, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h0, h1808, h1816, h1822, h1824, hc01, hc45, hlam, hphi, ht0b, ht5b, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        rcases p1825_3 (m.d 0 2) (by simp) with h1830 | h1830
                        · rcases p1825_3 (m.d 1 2) (by simp) with h1831 | h1831
                          · linarith only [h0, h1831, hlam]
                          · linarith only [h1816, h1831, hlam]
                        · linarith only [h1830, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h0, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1540, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1808, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1540, h1822, h1824, h2, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h2, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h2, h5, hc12, hc34, hlam, hphi, ht23, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1820, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1822, h1824, h2, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h3, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1816, h1822, h1824, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h0, h1822, h1824, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h4, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1816, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1822, hlam, p1825_1]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [h1823, hlam, p1825_0]
                      · have p1825_0 := h1825c.1
                        have p1825_1 := h1825c.2.1
                        have p1825_2 := h1825c.2.2.1
                        have p1825_3 := h1825c.2.2.2
                        linarith only [hlam, p1825_0]
                    · linarith only [h1540, h1816, h1822, h1824, h2, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                  · linarith only [h1808, h1816, h1819, h1823, hlam]
                · linarith only [h1540, h1816, h1822, hlam]
            · linarith only [h1540, h1816, h1817, h1819, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1859 | h1859
          · linarith only [h1540, h1859, h2, h5, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1861 | h1861
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1862 | h1862
              · linarith only [h1862, h2, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1864 | h1864
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1865 | h1865
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1866 | h1866
                    · rcases h2bigk with h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c | h1867c
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        rcases p1867_3 (m.d 0 2) (by simp) with h1869 | h1869
                        · rcases p1867_3 (m.d 1 2) (by simp) with h1870 | h1870
                          · linarith only [h0, h1870, hlam]
                          · rcases p1867_3 (m.d 2 3) (by simp) with h1872 | h1872
                            · linarith only [h1872, h2, hlam]
                            · linarith only [h1540, h1872, hlam]
                        · linarith only [h0, h1869, hlam]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h0, h1864, hc01, hc35, hlam, hphi, ht0b, ht5b, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h0, h1808, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h0, h1816, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h0, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h1540, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h1808, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h1816, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h2, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h1862, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h1816, hc12, hc23, hlam, hphi, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h3, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h0, h1816, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h4, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h1864, hc12, hc23, hlam, hphi, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h1864, hlam, p1867_1]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [h1865, hlam, p1867_0]
                      · have p1867_0 := h1867c.1
                        have p1867_1 := h1867c.2.1
                        have p1867_2 := h1867c.2.2.1
                        have p1867_3 := h1867c.2.2.2
                        linarith only [hlam, p1867_0]
                    · linarith only [h1, h1861, h1866, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1808, h1816, h1861, h1864, h1865, h2, h5, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1901 | h1901
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1902 | h1902
                    · rcases h2bigk with h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        rcases p1903_3 (m.d 0 2) (by simp) with h1905 | h1905
                        · rcases p1903_3 (m.d 1 2) (by simp) with h1906 | h1906
                          · linarith only [h0, h1906, hlam]
                          · rcases p1903_3 (m.d 2 3) (by simp) with h1908 | h1908
                            · linarith only [h1908, h2, hlam]
                            · linarith only [h1540, h1908, hlam]
                        · linarith only [h0, h1905, hlam]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1540, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1540, h1864, h1901, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1540, h1864, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1540, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1808, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1816, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h2, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1862, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1864, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h3, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1540, h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h4, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hc12, hc25, hlam, hphi, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1540, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1901, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                    · linarith only [h0, h1808, h1861, h1902, h3, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1808, h1861, h1901, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1937 | h1937
              · linarith only [h1539, h1540, h1859, h1861, h1937, h5, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1939 | h1939
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1940 | h1940
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1941 | h1941
                    · linarith only [h1540, h1859, h1861, h1939, h1941, h2, h5, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1939, h1940, h1941, h2, h5, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h1539, h1808, h1940, h5, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1945 | h1945
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1946 | h1946
                    · rcases h2bigk with h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c | h1947c
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        rcases p1947_3 (m.d 0 2) (by simp) with h1949 | h1949
                        · rcases p1947_3 (m.d 1 2) (by simp) with h1950 | h1950
                          · linarith only [h0, h1950, hlam]
                          · rcases p1947_3 (m.d 2 3) (by simp) with h1952 | h1952
                            · linarith only [h1952, h2, hlam]
                            · linarith only [h1540, h1952, hlam]
                        · linarith only [h0, h1949, hlam]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h0, h1540, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h0, h1540, h1859, h1861, h1945, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h0, h1540, h1859, h1861, h1945, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h0, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h1540, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h1808, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h1816, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h2, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h1937, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h1939, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h3, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [hc12, hc24, hlam, hphi, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h0, h1540, h1859, h1861, h1945, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h4, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [hc12, hc25, hlam, hphi, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h0, h1540, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1947_1]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [h1945, hlam, p1947_0]
                      · have p1947_0 := h1947c.1
                        have p1947_1 := h1947c.2.1
                        have p1947_2 := h1947c.2.2.1
                        have p1947_3 := h1947c.2.2.2
                        linarith only [hlam, p1947_0]
                    · linarith only [h1540, h1946, h2, h5, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h1539, h1808, h1945, h5, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1981 | h1981
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1982 | h1982
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1983 | h1983
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1984 | h1984
          · linarith only [h1, h1984, h5, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1986 | h1986
            · linarith only [h1, h1539, h1986, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1988 | h1988
              · linarith only [h1988, h2, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1990 | h1990
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1991 | h1991
                  · linarith only [h1, h1539, h1982, h1991, hlam]
                  · linarith only [h1988, h1990, h1991, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1994 | h1994
                  · linarith only [h1539, h1994, h3, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1996 | h1996
                    · rcases h2bigk with h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h0, h1981, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1997_1]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        rcases p1997_3 (m.d 0 2) (by simp) with h2000 | h2000
                        · rcases p1997_3 (m.d 1 2) (by simp) with h2001 | h2001
                          · linarith only [h0, h2001, hlam]
                          · linarith only [h1981, h2001, hlam]
                        · linarith only [h2000, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        rcases p1997_3 (m.d 0 2) (by simp) with h2005 | h2005
                        · rcases p1997_3 (m.d 1 2) (by simp) with h2006 | h2006
                          · linarith only [h0, h2006, hlam]
                          · linarith only [h1982, h2006, hlam]
                        · linarith only [h2005, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        rcases p1997_3 (m.d 0 2) (by simp) with h2010 | h2010
                        · rcases p1997_3 (m.d 1 2) (by simp) with h2011 | h2011
                          · linarith only [h0, h2011, hlam]
                          · linarith only [h1983, h2011, hlam]
                        · linarith only [h2010, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h0, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1997_1]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1997_1]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h0, h1994, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1997_1]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h2, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h1981, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h1988, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h1990, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h3, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h1982, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1997_1]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h1994, hlam, p1997_1]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h4, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h1983, hlam, p1997_0]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1997_1]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [h1539, h1996, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1997_1]
                      · have p1997_0 := h1997c.1
                        have p1997_1 := h1997c.2.1
                        have p1997_2 := h1997c.2.2.1
                        have p1997_3 := h1997c.2.2.2
                        linarith only [hlam, p1997_0]
                    · rcases h2bigk with h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h0, h1983, h1994, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2035_1]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        rcases p2035_3 (m.d 0 2) (by simp) with h2038 | h2038
                        · rcases p2035_3 (m.d 1 2) (by simp) with h2039 | h2039
                          · linarith only [h0, h2039, hlam]
                          · linarith only [h1981, h2039, hlam]
                        · linarith only [h2038, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        rcases p2035_3 (m.d 0 2) (by simp) with h2043 | h2043
                        · rcases p2035_3 (m.d 1 2) (by simp) with h2044 | h2044
                          · linarith only [h0, h2044, hlam]
                          · linarith only [h1982, h2044, hlam]
                        · linarith only [h2043, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        rcases p2035_3 (m.d 0 2) (by simp) with h2048 | h2048
                        · rcases p2035_3 (m.d 1 2) (by simp) with h2049 | h2049
                          · linarith only [h0, h2049, hlam]
                          · linarith only [h1983, h2049, hlam]
                        · linarith only [h2048, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h0, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2035_1]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h0, h1988, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2035_1]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h0, h1988, h1994, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2035_1]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h2, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h1981, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h1988, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h1990, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h3, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h1982, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2035_1]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h1994, hlam, p2035_1]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h4, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h1983, hlam, p2035_0]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2035_1]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [h0, h1983, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2035_1]
                      · have p2035_0 := h2035c.1
                        have p2035_1 := h2035c.2.1
                        have p2035_2 := h2035c.2.2.1
                        have p2035_3 := h2035c.2.2.2
                        linarith only [hlam, p2035_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2073 | h2073
          · linarith only [h0, h1981, h1983, h2073, h4, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2075 | h2075
            · linarith only [h1, h1539, h2075, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2077 | h2077
              · linarith only [h0, h1, h1981, h1983, h2073, h2077, h4, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2079 | h2079
                · linarith only [h0, h1981, h1983, h2079, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2081 | h2081
                  · linarith only [h0, h1982, h1983, h2081, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2083 | h2083
                    · linarith only [h1539, h1982, h1983, h2077, h2083, h4, hc23, hc34, hlam, hphi]
                    · rcases h2bigk with h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h1982, h2077, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        rcases p2085_3 (m.d 0 2) (by simp) with h2088 | h2088
                        · rcases p2085_3 (m.d 1 2) (by simp) with h2089 | h2089
                          · linarith only [h0, h2089, hlam]
                          · linarith only [h1981, h2089, hlam]
                        · linarith only [h2088, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        rcases p2085_3 (m.d 0 2) (by simp) with h2093 | h2093
                        · rcases p2085_3 (m.d 1 2) (by simp) with h2094 | h2094
                          · linarith only [h0, h2094, hlam]
                          · linarith only [h1982, h2094, hlam]
                        · linarith only [h2093, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h0, h1982, h1983, h2077, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h0, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h1983, h4, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h0, h1983, h2077, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h1983, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h2, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h1981, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h2077, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h2079, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h3, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h1982, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h2081, hlam, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h4, hlam, p2085_0]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h0, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [h0, h2077, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2085_1]
                      · have p2085_0 := h2085c.1
                        have p2085_1 := h2085c.2.1
                        have p2085_2 := h2085c.2.2.1
                        have p2085_3 := h2085c.2.2.2
                        linarith only [hlam, p2085_0]
      · linarith only [h1539, h1981, h1982, h3, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2120 | h2120
      · linarith only [h1539, h1981, h2, h2120, h5, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2122 | h2122
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2123 | h2123
          · linarith only [h1981, h2, h2122, h2123, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2125 | h2125
            · linarith only [h1539, h1981, h2, h2122, h2125, h5, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h2120, h2122, h2125, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2128 | h2128
          · linarith only [h1981, h2, h2128, h5, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2130 | h2130
            · linarith only [h1, h1539, h1981, h2, h2130, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2132 | h2132
              · linarith only [h2, h2132, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2134 | h2134
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2135 | h2135
                  · linarith only [h1539, h2135, h3, hlam]
                  · linarith only [h2132, h2134, h2135, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2138 | h2138
                  · linarith only [h1539, h1981, h2, h2138, h5, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2140 | h2140
                    · linarith only [h1539, h1981, h2, h2140, h5, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1981, h2, h2140, h5, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0 m hb2 hb4 hg0 hg1 h2 h3 h4 h5
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x1 m hb2 hb4 hg0 hg1 h2 h3 h4 h5

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h2143 | h2143
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2144 | h2144
    · linarith only [h2, h2143, h2144, h4, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2146 | h2146
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2147 | h2147
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2148 | h2148
          · linarith only [h0, h2148, h4, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2150 | h2150
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2151 | h2151
              · linarith only [h1, h2144, h2151, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2153 | h2153
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2154 | h2154
                  · linarith only [h0, h2146, h2154, h4, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2156 | h2156
                    · linarith only [h0, h1, h2144, h2146, h2153, h2156, h4, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h2146, h2153, h2156, h4, hc34, hc45, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2159 | h2159
                  · linarith only [h0, h2146, h2150, h2153, h2159, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h2146, h2150, h2153, h2159, h4, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2162 | h2162
              · linarith only [h1, h2144, h2162, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2164 | h2164
                · linarith only [h2146, h2150, h2164, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2166 | h2166
                  · linarith only [h2, h2143, h2146, h2150, h2166, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h2, h2143, h2146, h2150, h2166, h4, hc23, hc35, hlam, hphi]
        · linarith only [h2147, h3, h4, hc12, hc25, hlam, hphi]
      · linarith only [h2, h2146, h4, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2171 | h2171
    · linarith only [h2171, h3, h4, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2173 | h2173
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2174 | h2174
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2175 | h2175
          · linarith only [h0, h2175, h4, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2177 | h2177
            · linarith only [h1, h2143, h2177, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2179 | h2179
              · linarith only [h1, h2171, h2179, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2181 | h2181
                · linarith only [h2, h2143, h2181, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2183 | h2183
                  · linarith only [h0, h2174, h2181, h2183, h4, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2185 | h2185
                    · linarith only [h0, h2171, h2174, h2183, h2185, h4, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2187 | h2187
                      · linarith only [h0, h2174, h2181, h2185, h2187, h4, hc23, hc34, hlam, hphi]
                      · rcases h2bigk with h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2174, h2181, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2181, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h4, hlam, p2189_0]
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
                          linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h0, h2181, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2175, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2173, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2181, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2183, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h3, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2174, hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h3, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2185, hlam, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hc02, hc25, hlam, hphi, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2173, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2183, h2187, hc23, hc45, hlam, hphi, ht34, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [h2181, h2183, h2187, hc23, hc45, hlam, hphi, ht34, p2189_1]
                        · have p2189_0 := h2189c.1
                          have p2189_1 := h2189c.2.1
                          have p2189_2 := h2189c.2.2.1
                          have p2189_3 := h2189c.2.2.2
                          linarith only [hlam, p2189_0]
        · linarith only [h2174, h3, h4, hc12, hc25, hlam, hphi]
      · linarith only [h2, h2173, h4, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0_x0 m hb2 hb4 hg0 hg1 h2 h3 h4
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0_x1 m hb2 hb4 hg0 hg1 h2 h3 h4

end R2N4
