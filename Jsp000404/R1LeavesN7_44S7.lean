import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h1538 | h1538
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1539 | h1539
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1540 | h1540
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1541 | h1541
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1542 | h1542
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1543 | h1543
            · linarith only [h1, h1543, h5, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1545 | h1545
              · linarith only [h1542, h1543, h1545, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1547 | h1547
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1548 | h1548
                  · linarith only [h1, h1539, h1548, h5, hc12, hlam, hphi, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1550 | h1550
                    · linarith only [h1539, h1545, h1547, h1550, hc13, hlam, hphi, u1ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1552 | h1552
                      · linarith only [h1545, h1552, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                      · linarith only [h1538, h1552, h5, hlam]
                · linarith only [h1, h1542, h1547, h5, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1556 | h1556
            · linarith only [h1542, h1556, h5, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1558 | h1558
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1559 | h1559
                · linarith only [h1542, h1559, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1561 | h1561
                  · linarith only [h1, h1539, h1561, h5, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1563 | h1563
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1564 | h1564
                      · rcases h1bigk with h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h1540, h1563, hc01, hc45, hlam, hphi, ht0b, ht5b, p1565_1]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          rcases p1565_3 (m.d 0 1) (by simp) with h1568 | h1568
                          · rcases p1565_3 (m.d 1 2) (by simp) with h1569 | h1569
                            · linarith only [h0, h1569, hlam]
                            · linarith only [h1539, h1569, hlam]
                          · linarith only [h1568, hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          rcases p1565_3 (m.d 0 1) (by simp) with h1573 | h1573
                          · rcases p1565_3 (m.d 1 2) (by simp) with h1574 | h1574
                            · linarith only [h0, h1574, hlam]
                            · linarith only [h1540, h1574, hlam]
                          · linarith only [h1573, hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          rcases p1565_3 (m.d 0 1) (by simp) with h1578 | h1578
                          · rcases p1565_3 (m.d 1 2) (by simp) with h1579 | h1579
                            · linarith only [h0, h1579, hlam]
                            · linarith only [h1541, h1579, hlam]
                          · linarith only [h1578, hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h0, hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [hc12, hlam, hphi, p1565_1, u1ehi2]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1565_1, u1ehi3]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h0, h1556, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1565_1, u1ehi2]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h1, hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h1539, hlam, p1565_1]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h1542, hlam, p1565_1]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h1556, hlam, p1565_1]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h2, hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h1540, hlam, p1565_1]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [hc14, hlam, hphi, p1565_1, u1ehi2]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h0, h1540, h1556, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1565_1, u1ehi2]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h3, hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h1541, hlam, p1565_1]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [hc15, hlam, hphi, p1565_1, u1ehi2]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [h1558, hlam, p1565_0]
                        · have p1565_0 := h1565c.1
                          have p1565_1 := h1565c.2.1
                          have p1565_2 := h1565c.2.2.1
                          have p1565_3 := h1565c.2.2.2
                          linarith only [hlam, p1565_0]
                      · linarith only [h1542, h1563, h1564, hc24, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1604 | h1604
                      · rcases h1bigk with h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1540, h1558, h1559, h1563, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          rcases p1605_3 (m.d 0 1) (by simp) with h1608 | h1608
                          · rcases p1605_3 (m.d 1 2) (by simp) with h1609 | h1609
                            · linarith only [h0, h1609, hlam]
                            · linarith only [h1539, h1609, hlam]
                          · linarith only [h1608, hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1558, h1559, h1563, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          rcases p1605_3 (m.d 0 1) (by simp) with h1614 | h1614
                          · rcases p1605_3 (m.d 1 2) (by simp) with h1615 | h1615
                            · linarith only [h0, h1615, hlam]
                            · linarith only [h1541, h1615, hlam]
                          · linarith only [h1614, hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h0, hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [hc12, hlam, hphi, p1605_1, u1ehi2]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h0, h1558, h1559, h1563, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h0, h1556, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1605_1, u1ehi2]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1, hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1539, hlam, p1605_1]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1542, hlam, p1605_1]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1556, hlam, p1605_1]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h2, hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1540, hlam, p1605_1]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [hc14, hlam, hphi, p1605_1, u1ehi2]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h0, h1540, h1556, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1605_1, u1ehi2]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h3, hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1541, hlam, p1605_1]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [hc15, hlam, hphi, p1605_1, u1ehi2]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [h1558, hlam, p1605_0]
                        · have p1605_0 := h1605c.1
                          have p1605_1 := h1605c.2.1
                          have p1605_2 := h1605c.2.2.1
                          have p1605_3 := h1605c.2.2.2
                          linarith only [hlam, p1605_0]
                      · linarith only [h1542, h1604, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1640 | h1640
                · linarith only [h1542, h1640, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1642 | h1642
                  · linarith only [h1539, h1542, h1642, h5, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1644 | h1644
                    · linarith only [h1542, h1558, h1644, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1646 | h1646
                      · linarith only [h1542, h1558, h1646, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h1538, h1542, h1646, h5, hc35, hlam, hphi, ht12, ht23, u1ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1649 | h1649
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1650 | h1650
            · linarith only [h1, h1650, h5, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1652 | h1652
              · linarith only [h1539, h1541, h1649, h1652, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1654 | h1654
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1655 | h1655
                  · linarith only [h0, h1539, h1655, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1657 | h1657
                    · linarith only [h1539, h1541, h1652, h1654, h1655, h1657, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                    · linarith only [h1539, h1541, h1654, h1657, hc34, hc45, hlam, hphi]
                · linarith only [h1, h1649, h1654, h5, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1661 | h1661
            · linarith only [h1, h1661, h5, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1663 | h1663
              · linarith only [h1540, h1541, h1663, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1665 | h1665
                · linarith only [h1649, h1665, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1667 | h1667
                  · linarith only [h1538, h1540, h1541, h1649, h1663, h1665, h1667, h2, h5, hc01, hc03, hc25, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1669 | h1669
                    · linarith only [h1540, h1541, h1649, h1663, h1667, h1669, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1671 | h1671
                      · linarith only [h1540, h1541, h1665, h1669, h1671, hc23, hc34, hlam, hphi]
                      · linarith only [h1538, h1649, h1671, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1674 | h1674
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1675 | h1675
          · linarith only [h1539, h1540, h1675, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1677 | h1677
            · linarith only [h1539, h1540, h1677, h3, h5, hc24, hlam, hphi, ht12, u1ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1679 | h1679
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1680 | h1680
                · linarith only [h1539, h1540, h1675, h1680, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1682 | h1682
                  · linarith only [h1539, h1540, h1680, h1682, h5, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1684 | h1684
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1685 | h1685
                      · rcases h1bigk with h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          rcases p1686_3 (m.d 0 1) (by simp) with h1688 | h1688
                          · rcases p1686_3 (m.d 1 2) (by simp) with h1689 | h1689
                            · linarith only [h1689, hlam, p1686_0]
                            · rcases p1686_3 (m.d 1 3) (by simp) with h1691 | h1691
                              · linarith only [h1, h1691, hlam]
                              · rcases p1686_3 (m.d 1 4) (by simp) with h1693 | h1693
                                · linarith only [h1693, h2, hlam]
                                · linarith only [h1540, h1693, hlam]
                          · linarith only [h1688, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          rcases p1686_3 (m.d 0 1) (by simp) with h1697 | h1697
                          · rcases p1686_3 (m.d 1 2) (by simp) with h1698 | h1698
                            · linarith only [h0, h1698, hlam]
                            · linarith only [h1539, h1698, hlam]
                          · linarith only [h1697, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          rcases p1686_3 (m.d 0 1) (by simp) with h1702 | h1702
                          · rcases p1686_3 (m.d 1 2) (by simp) with h1703 | h1703
                            · linarith only [h0, h1703, hlam]
                            · rcases p1686_3 (m.d 1 3) (by simp) with h1705 | h1705
                              · linarith only [h1, h1705, hlam]
                              · rcases p1686_3 (m.d 1 4) (by simp) with h1707 | h1707
                                · linarith only [h1707, hlam, p1686_0]
                                · rcases p1686_3 (m.d 1 5) (by simp) with h1709 | h1709
                                  · linarith only [h1709, h3, hlam]
                                  · rcases h5bigk with h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1677, h5, hc35, hlam, hphi, ht12, ht23, p1711_1, u1ehi2]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      rcases p1711_3 (m.d 0 5) (by simp) with h1714 | h1714
                                      · rcases p1711_3 (m.d 1 5) (by simp) with h1715 | h1715
                                        · linarith only [h1715, h3, hlam]
                                        · linarith only [h1674, h1715, hlam]
                                      · linarith only [h1714, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h5, hlam, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      rcases p1711_3 (m.d 0 5) (by simp) with h1720 | h1720
                                      · rcases p1711_3 (m.d 1 5) (by simp) with h1721 | h1721
                                        · linarith only [h1721, h3, hlam]
                                        · linarith only [h1679, h1721, hlam]
                                      · linarith only [h1538, h1720, hlam]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h3, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1540, h1674, h1682, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1686_1, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1677, hlam, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1540, h1674, hc01, hc45, hlam, hphi, ht0b, ht5b, p1686_1, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h3, hc25, hlam, hphi, ht12, p1711_1, u1ehi4]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1674, hlam, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1682, hlam, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1540, h1674, hc01, hc45, hlam, hphi, ht0b, ht5b, p1686_1, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1, h1685, h5, hc34, hlam, hphi, ht12, ht23, p1711_1, u1ehi2]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1677, h1685, hc34, hlam, hphi, ht12, ht23, p1711_1, u1ehi2]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      rcases p1711_3 (m.d 0 5) (by simp) with h1737 | h1737
                                      · linarith only [h1737, h5, hlam]
                                      · linarith only [h1, h1540, h1674, h1737, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1686_1, u1ehi2]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      rcases p1711_3 (m.d 0 5) (by simp) with h1741 | h1741
                                      · linarith only [h1741, h5, hlam]
                                      · linarith only [h1538, h1741, hlam]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1538, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1679, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1684, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1685, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                          · linarith only [h1702, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          rcases p1686_3 (m.d 0 1) (by simp) with h1750 | h1750
                          · rcases p1686_3 (m.d 1 2) (by simp) with h1751 | h1751
                            · linarith only [h0, h1751, hlam]
                            · linarith only [h1674, h1751, hlam]
                          · linarith only [h1750, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h0, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [hc12, hlam, hphi, p1686_1, u1ehi2]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1540, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1540, h1677, hc24, hlam, hphi, ht12, p1686_1, u1ehi2]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1539, hlam, p1686_1]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1675, hlam, p1686_1]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1677, hlam, p1686_1]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h2, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1674, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1686_1]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1686_1, u1ehi2]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1677, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1686_1, u1ehi2]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h3, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1674, hlam, p1686_1]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1674, hc12, hlam, hphi, p1686_1, u1ehi2]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [h1679, hlam, p1686_0]
                        · have p1686_0 := h1686c.1
                          have p1686_1 := h1686c.2.1
                          have p1686_2 := h1686c.2.2.1
                          have p1686_3 := h1686c.2.2.2
                          linarith only [hlam, p1686_0]
                      · linarith only [h1540, h1680, h1685, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h1540, h1674, h1679, h1684, hlam]
              · linarith only [h1540, h1674, h1679, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1778 | h1778
          · linarith only [h1539, h1540, h1778, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1780 | h1780
            · linarith only [h1, h1780, h5, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1782 | h1782
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1783 | h1783
                · linarith only [h1778, h1783, h4, h5, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1785 | h1785
                  · linarith only [h1539, h1540, h1785, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1787 | h1787
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1788 | h1788
                      · rcases h1bigk with h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c | h1789c
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          rcases p1789_3 (m.d 0 1) (by simp) with h1791 | h1791
                          · rcases p1789_3 (m.d 1 2) (by simp) with h1792 | h1792
                            · linarith only [h1792, hlam, p1789_0]
                            · rcases p1789_3 (m.d 1 3) (by simp) with h1794 | h1794
                              · linarith only [h1, h1794, hlam]
                              · rcases p1789_3 (m.d 1 4) (by simp) with h1796 | h1796
                                · linarith only [h1796, h2, hlam]
                                · linarith only [h1540, h1796, hlam]
                          · linarith only [h1791, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          rcases p1789_3 (m.d 0 1) (by simp) with h1800 | h1800
                          · rcases p1789_3 (m.d 1 2) (by simp) with h1801 | h1801
                            · linarith only [h0, h1801, hlam]
                            · linarith only [h1539, h1801, hlam]
                          · linarith only [h1800, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          rcases p1789_3 (m.d 0 1) (by simp) with h1805 | h1805
                          · rcases p1789_3 (m.d 1 2) (by simp) with h1806 | h1806
                            · linarith only [h0, h1806, hlam]
                            · rcases p1789_3 (m.d 1 3) (by simp) with h1808 | h1808
                              · linarith only [h1, h1808, hlam]
                              · rcases p1789_3 (m.d 1 4) (by simp) with h1810 | h1810
                                · linarith only [h1810, hlam, p1789_0]
                                · rcases p1789_3 (m.d 1 5) (by simp) with h1812 | h1812
                                  · linarith only [h1812, h3, hlam]
                                  · rcases h5bigk with h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1539, h1674, h5, hc23, hc35, hlam, hphi, p1814_1]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1539, h1674, h1788, h5, hc34, hlam, hphi, ht12, ht23, p1814_1, u1ehi2]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h5, hlam, p1814_1]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      rcases p1814_3 (m.d 0 5) (by simp) with h1819 | h1819
                                      · rcases p1814_3 (m.d 1 5) (by simp) with h1820 | h1820
                                        · linarith only [h1820, h3, hlam]
                                        · linarith only [h1782, h1820, hlam]
                                      · linarith only [h1538, h1819, hlam]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h3, hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1674, hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1780, hlam, p1814_1]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1782, hc01, hc45, hlam, hphi, ht0b, ht5b, p1789_1, p1814_1]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1539, h1674, h1787, h3, hc24, hlam, hphi, ht12, p1814_1, u1ehi2]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1539, h1674, h1787, hc24, hlam, hphi, ht12, p1814_1, u1ehi2]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1785, hlam, p1814_1]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      rcases p1814_3 (m.d 0 5) (by simp) with h1833 | h1833
                                      · rcases p1814_3 (m.d 1 5) (by simp) with h1834 | h1834
                                        · linarith only [h1674, h1834, hlam]
                                        · linarith only [h1782, h1834, hlam]
                                      · linarith only [h1538, h1833, hlam]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1539, h1674, h1788, h3, hc34, hlam, hphi, ht12, ht23, p1814_1, u1ehi2]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1539, h1674, h1788, hc34, hlam, hphi, ht12, ht23, p1814_1, u1ehi2]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1539, h1674, h1788, hc34, hlam, hphi, ht12, ht23, p1814_1, u1ehi2]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      rcases p1814_3 (m.d 0 5) (by simp) with h1842 | h1842
                                      · linarith only [h1842, h5, hlam]
                                      · linarith only [h1538, h1842, hlam]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1538, hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1782, hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1787, hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [h1788, hlam, p1814_0]
                                    · have p1814_0 := h1814c.1
                                      have p1814_1 := h1814c.2.1
                                      have p1814_2 := h1814c.2.2.1
                                      have p1814_3 := h1814c.2.2.2
                                      linarith only [hlam, p1814_0]
                          · linarith only [h1805, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          rcases p1789_3 (m.d 0 1) (by simp) with h1851 | h1851
                          · rcases p1789_3 (m.d 1 2) (by simp) with h1852 | h1852
                            · linarith only [h0, h1852, hlam]
                            · rcases p1789_3 (m.d 1 3) (by simp) with h1854 | h1854
                              · linarith only [h1, h1854, hlam]
                              · rcases p1789_3 (m.d 1 4) (by simp) with h1856 | h1856
                                · linarith only [h1856, h2, hlam]
                                · linarith only [h1782, h1856, hlam]
                          · linarith only [h1851, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h0, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [hc12, hlam, hphi, p1789_1, u1ehi2]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h1540, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h1674, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h1, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h1539, hlam, p1789_1]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h1778, hlam, p1789_1]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h1780, hlam, p1789_1]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h2, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1789_1, u1ehi1]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1789_1, u1ehi2]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1789_1, u1ehi4]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h3, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h1539, hc15, hlam, hphi, p1789_1, u1ehi2]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1789_1, u1ehi2]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [h1782, hlam, p1789_0]
                        · have p1789_0 := h1789c.1
                          have p1789_1 := h1789c.2.1
                          have p1789_2 := h1789c.2.2.1
                          have p1789_3 := h1789c.2.2.2
                          linarith only [hlam, p1789_0]
                      · linarith only [h1538, h1539, h1540, h1783, h1788, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · linarith only [h1540, h1782, h1787, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1882 | h1882
                · linarith only [h1538, h1539, h1540, h1782, h1882, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1884 | h1884
                  · linarith only [h1538, h1539, h1540, h1782, h1884, h5, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1886 | h1886
                    · linarith only [h1539, h1540, h1782, h1882, h1886, hc23, hc34, hlam, hphi]
                    · linarith only [h1538, h1539, h1540, h1886, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
    · linarith only [h1539, h4, h5, hc35, hlam, hphi, ht12, ht23, u1ehi1]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1890 | h1890
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1891 | h1891
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1892 | h1892
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1893 | h1893
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1894 | h1894
            · linarith only [h1, h1894, h5, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1896 | h1896
              · linarith only [h1538, h1896, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1898 | h1898
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1899 | h1899
                  · linarith only [h1, h1890, h1899, h5, hc12, hlam, hphi, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1901 | h1901
                    · linarith only [h0, h1538, h1892, h1898, h1899, h1901, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1903 | h1903
                      · linarith only [h0, h1538, h1892, h1898, h1899, h1903, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                      · rcases h1bigk with h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1892, h1898, h1899, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1905_1]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          rcases p1905_3 (m.d 0 1) (by simp) with h1908 | h1908
                          · rcases p1905_3 (m.d 1 2) (by simp) with h1909 | h1909
                            · linarith only [h0, h1909, hlam]
                            · linarith only [h1890, h1909, hlam]
                          · linarith only [h1908, hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          rcases p1905_3 (m.d 0 1) (by simp) with h1913 | h1913
                          · rcases p1905_3 (m.d 1 2) (by simp) with h1914 | h1914
                            · linarith only [h0, h1914, hlam]
                            · linarith only [h1891, h1914, hlam]
                          · linarith only [h1913, hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          rcases p1905_3 (m.d 0 1) (by simp) with h1918 | h1918
                          · rcases p1905_3 (m.d 1 2) (by simp) with h1919 | h1919
                            · linarith only [h0, h1919, hlam]
                            · linarith only [h1892, h1919, hlam]
                          · linarith only [h1918, hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h0, hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1893, hc12, hlam, hphi, p1905_1, u1ehi3]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1905_1, u1ehi3]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1905_1, u1ehi4]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1, hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1890, hlam, p1905_1]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [hc13, hlam, hphi, p1905_1, u1ehi3]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1894, hlam, p1905_1]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h2, hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1891, hlam, p1905_1]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1893, hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1896, hlam, p1905_1]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h3, hlam, p1905_0]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1892, hlam, p1905_1]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [hc15, hlam, hphi, p1905_1, u1ehi2]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [h1903, h3, h5, hc45, hlam, hphi, ht12, ht23, ht34, p1905_1, u1ehi3]
                        · have p1905_0 := h1905c.1
                          have p1905_1 := h1905c.2.1
                          have p1905_2 := h1905c.2.2.1
                          have p1905_3 := h1905c.2.2.2
                          linarith only [hlam, p1905_0]
                · linarith only [h1, h1893, h1898, h5, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1944 | h1944
            · linarith only [h1893, h1944, h5, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1946 | h1946
              · linarith only [h1538, h1946, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1948 | h1948
                · linarith only [h1893, h1948, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1950 | h1950
                  · linarith only [h1890, h1893, h1950, h5, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1952 | h1952
                    · linarith only [h1538, h1893, h1952, h2, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1954 | h1954
                      · linarith only [h1538, h1893, h1954, h2, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h1893, h1954, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1957 | h1957
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1958 | h1958
            · linarith only [h1, h1958, h5, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1960 | h1960
              · linarith only [h1538, h1960, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1962 | h1962
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1963 | h1963
                  · linarith only [h1, h1957, h1963, h5, hc23, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1965 | h1965
                    · linarith only [h1538, h1965, h2, hc24, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h1890, h1892, h1962, h1965, hc34, hc45, hlam, hphi]
                · linarith only [h1, h1957, h1962, h5, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1969 | h1969
            · linarith only [h1957, h1969, h5, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1971 | h1971
              · linarith only [h1538, h1971, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1973 | h1973
                · linarith only [h1957, h1973, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1975 | h1975
                  · linarith only [h1, h1975, h5, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1977 | h1977
                    · linarith only [h1538, h1891, h1892, h1957, h1975, h1977, h2, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1979 | h1979
                      · linarith only [h1891, h1892, h1973, h1977, h1979, hc23, hc34, hlam, hphi]
                      · linarith only [h1957, h1979, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1982 | h1982
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1983 | h1983
          · linarith only [h1890, h1891, h1983, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1985 | h1985
            · linarith only [h1, h1985, h5, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1987 | h1987
              · linarith only [h1538, h1987, h2, hlam]
              · linarith only [h1891, h1982, h1987, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1990 | h1990
          · linarith only [h1890, h1891, h1990, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1992 | h1992
            · linarith only [h1, h1992, h5, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1994 | h1994
              · linarith only [h1538, h1994, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1996 | h1996
                · linarith only [h1890, h1891, h1990, h1996, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1998 | h1998
                  · linarith only [h1, h1538, h1890, h1891, h1998, h2, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2000 | h2000
                    · linarith only [h1538, h1890, h1891, h1996, h2, h2000, hc23, hc34, hlam, hphi]
                    · linarith only [h1890, h1891, h2000, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · linarith only [h1890, h4, h5, hc35, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_21_15_M_IR_L_I_s3_x0_x0 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_21_15_M_IR_L_I_s3_x0_x1 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h5

end R2N4
