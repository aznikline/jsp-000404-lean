import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1534 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1535 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1536 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1537 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 5 (by decide) (by decide) with h1538 | h1538
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1539 | h1539
    · rcases m.htr 3 4 5 (by decide) (by decide) with h1540 | h1540
      · linarith only [h1525, h1537, h1540, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
      · rcases h2bigk with h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h0, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h0, h1537, h1539, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1542_1]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h0, h1539, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1542_1]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          rcases p1542_3 (m.d 0 2) (by simp) with h1547 | h1547
          · rcases p1542_3 (m.d 1 2) (by simp) with h1548 | h1548
            · rcases p1542_3 (m.d 2 3) (by simp) with h1549 | h1549
              · linarith only [h1525, h1549, hlam]
              · linarith only [h1538, h1549, hlam]
            · linarith only [h1533, h1548, hlam]
          · linarith only [h1547, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h0, hc12, hlam, hphi, p1542_1, u1ehi0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1537, h1539, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1542_1]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1539, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1542_1]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          rcases p1542_3 (m.d 0 2) (by simp) with h1558 | h1558
          · linarith only [h0, h1558, hlam]
          · linarith only [h1527, h1558, hlam]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1525, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1531, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1525, h1539, h1540, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1542_1]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h0, h1525, h1539, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1542_1]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1526, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1532, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1537, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h0, h1526, h1539, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1542_1]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1527, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1533, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1538, hlam, p1542_0]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [h1539, hlam, p1542_1]
        · have p1542_0 := h1542c.1
          have p1542_1 := h1542c.2.1
          have p1542_2 := h1542c.2.2.1
          have p1542_3 := h1542c.2.2.2
          linarith only [hlam, p1542_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h1576 | h1576
      · linarith only [h0, h1525, h1537, h1539, h1576, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h2bigk with h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c | h1578c
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h0, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h0, h1538, hc12, hlam, hphi, ht01, ht0b, ht5b, p1578_1, u5ehi3]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          rcases p1578_3 (m.d 0 2) (by simp) with h1582 | h1582
          · rcases p1578_3 (m.d 1 2) (by simp) with h1583 | h1583
            · rcases p1578_3 (m.d 2 3) (by simp) with h1584 | h1584
              · linarith only [h1525, h1584, hlam]
              · linarith only [h1537, h1584, hlam]
            · linarith only [h1532, h1583, hlam]
          · linarith only [h1582, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          rcases p1578_3 (m.d 0 2) (by simp) with h1589 | h1589
          · rcases p1578_3 (m.d 1 2) (by simp) with h1590 | h1590
            · rcases p1578_3 (m.d 2 3) (by simp) with h1591 | h1591
              · linarith only [h1525, h1591, hlam]
              · linarith only [h1538, h1591, hlam]
            · linarith only [h1533, h1590, hlam]
          · linarith only [h1589, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h0, hc12, hlam, hphi, p1578_1, u1ehi0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1538, hc12, hlam, hphi, ht01, ht0b, ht5b, p1578_1, u5ehi3]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          rcases p1578_3 (m.d 0 2) (by simp) with h1599 | h1599
          · linarith only [h0, h1599, hlam]
          · linarith only [h1526, h1599, hlam]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          rcases p1578_3 (m.d 0 2) (by simp) with h1602 | h1602
          · linarith only [h0, h1602, hlam]
          · linarith only [h1527, h1602, hlam]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1525, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1531, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          rcases p1578_3 (m.d 0 2) (by simp) with h1608 | h1608
          · rcases p1578_3 (m.d 1 2) (by simp) with h1609 | h1609
            · rcases p1578_3 (m.d 2 3) (by simp) with h1610 | h1610
              · rcases p1578_3 (m.d 2 4) (by simp) with h1611 | h1611
                · linarith only [h1537, h1611, hlam]
                · rcases p1578_3 (m.d 2 5) (by simp) with h1613 | h1613
                  · linarith only [h1538, h1613, hlam]
                  · linarith only [h1539, h1613, hlam]
              · linarith only [h1537, h1610, hlam]
            · linarith only [h1532, h1609, hlam]
          · linarith only [h1526, h1608, hlam]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1525, h1538, hc02, hlam, hphi, ht0b, ht5b, p1578_1, u5ehi3]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1526, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1532, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1537, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1539, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1527, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1533, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [h1538, hlam, p1578_0]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          rcases p1578_3 (m.d 0 2) (by simp) with h1628 | h1628
          · rcases p1578_3 (m.d 1 2) (by simp) with h1629 | h1629
            · rcases p1578_3 (m.d 2 3) (by simp) with h1630 | h1630
              · rcases p1578_3 (m.d 2 4) (by simp) with h1631 | h1631
                · linarith only [h1539, h1631, hlam]
                · rcases p1578_3 (m.d 2 5) (by simp) with h1633 | h1633
                  · rcases h2emax with h1634 | h1634 | h1634 | h1634 | h1634
                    · linarith only [h0, h1634, hlam, ht12, u1ehi0]
                    · linarith only [h1634, hlam, ht12, u1ehi1]
                    · linarith only [h1538, h1634, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases h4bigk with h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1521, hlam, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1530, h1539, hlam, p1578_1, p1638_2]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1530, h1537, h1539, hlam, p1578_1, p1638_2]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1525, h1528, h1537, h1539, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1578_1, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1521, hc14, hlam, hphi, p1638_1, u1ehi0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1521, h1530, h1539, hlam, p1578_1, p1638_2]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1521, h1530, h1537, h1539, hlam, p1578_1, p1638_2]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1537, h1539, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1578_1, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1526, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1532, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1530, h1539, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1578_1, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1539, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1528, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1534, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1537, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1576, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1530, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1536, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        rcases p1638_3 (m.d 0 4) (by simp) with h1661 | h1661
                        · rcases p1638_3 (m.d 1 4) (by simp) with h1662 | h1662
                          · rcases p1638_3 (m.d 2 4) (by simp) with h1663 | h1663
                            · linarith only [h1663, hlam, p1638_0]
                            · rcases p1638_3 (m.d 3 4) (by simp) with h1665 | h1665
                              · linarith only [h1576, h1665, hlam]
                              · rcases p1638_3 (m.d 4 5) (by simp) with h1667 | h1667
                                · rcases h5bigk with h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [hlam, p1668_0]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1523, hlam, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p1578_1, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    rcases p1668_3 (m.d 0 5) (by simp) with h1672 | h1672
                                    · rcases p1668_3 (m.d 1 5) (by simp) with h1673 | h1673
                                      · rcases p1668_3 (m.d 2 5) (by simp) with h1674 | h1674
                                        · linarith only [h1527, h1674, hlam]
                                        · linarith only [h1538, h1674, hlam]
                                      · linarith only [h1535, h1673, hlam]
                                    · linarith only [h1529, h1672, hlam]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1537, h1539, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1578_1, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1523, hc15, hlam, hphi, p1668_1, u1ehi0]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [hlam, p1668_0]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1533, h1537, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1578_1, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    rcases p1668_3 (m.d 0 5) (by simp) with h1683 | h1683
                                    · linarith only [h1523, h1683, hlam]
                                    · linarith only [h1529, h1683, hlam]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1534, h1536, h1537, h1539, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1578_1, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1527, hlam, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1533, hlam, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [hlam, p1668_0]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1525, h1528, h1530, h1539, hc02, hlam, hphi, ht0b, ht5b, p1668_1, u5ehi3]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1539, hlam, p1668_0]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1529, hlam, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1535, hlam, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1538, hlam, p1668_0]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [hlam, p1668_0]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1576, hlam, p1668_0]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1530, hlam, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1536, hlam, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h1525, h1528, h1530, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p1578_1, p1668_1]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [h0, h1525, h1528, h1530, hc12, hlam, hphi, ht01, ht0b, ht5b, p1668_1, u5ehi3]
                                  · have p1668_0 := h1668c.1
                                    have p1668_1 := h1668c.2.1
                                    have p1668_2 := h1668c.2.2.1
                                    have p1668_3 := h1668c.2.2.2
                                    linarith only [hlam, p1668_0]
                                · linarith only [h1667, hlam, p1638_0]
                          · linarith only [h1532, h1662, hlam]
                        · linarith only [h1526, h1661, hlam]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        rcases p1638_3 (m.d 0 4) (by simp) with h1705 | h1705
                        · rcases p1638_3 (m.d 1 4) (by simp) with h1706 | h1706
                          · rcases p1638_3 (m.d 2 4) (by simp) with h1707 | h1707
                            · linarith only [h1539, h1707, hlam]
                            · linarith only [h1537, h1707, hlam]
                          · linarith only [h1534, h1706, hlam]
                        · linarith only [h1528, h1705, hlam]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                    · linarith only [h1537, h1634, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1578_1]
                  · linarith only [h1539, h1633, hlam]
              · linarith only [h1537, h1630, hlam]
            · linarith only [h1532, h1629, hlam]
          · linarith only [h1526, h1628, hlam]
        · have p1578_0 := h1578c.1
          have p1578_1 := h1578c.2.1
          have p1578_2 := h1578c.2.2.1
          have p1578_3 := h1578c.2.2.2
          linarith only [hlam, p1578_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1719 | h1719
    · linarith only [h0, h1525, h1529, h1537, h1538, h1719, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h1721 | h1721
      · linarith only [h0, h1525, h1529, h1537, h1538, h1719, h1721, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h2bigk with h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h0, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          rcases p1723_3 (m.d 0 2) (by simp) with h1726 | h1726
          · rcases p1723_3 (m.d 1 2) (by simp) with h1727 | h1727
            · rcases p1723_3 (m.d 2 3) (by simp) with h1728 | h1728
              · linarith only [h1728, hlam, p1723_0]
              · rcases p1723_3 (m.d 2 4) (by simp) with h1730 | h1730
                · linarith only [h1526, h1730, hlam]
                · rcases p1723_3 (m.d 2 5) (by simp) with h1732 | h1732
                  · linarith only [h1527, h1732, hlam]
                  · linarith only [h1538, h1732, hlam]
            · linarith only [h1531, h1727, hlam]
          · linarith only [h1726, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          rcases p1723_3 (m.d 0 2) (by simp) with h1737 | h1737
          · rcases p1723_3 (m.d 1 2) (by simp) with h1738 | h1738
            · rcases p1723_3 (m.d 2 3) (by simp) with h1739 | h1739
              · linarith only [h1525, h1739, hlam]
              · linarith only [h1537, h1739, hlam]
            · linarith only [h1532, h1738, hlam]
          · linarith only [h1737, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          rcases p1723_3 (m.d 0 2) (by simp) with h1744 | h1744
          · rcases p1723_3 (m.d 1 2) (by simp) with h1745 | h1745
            · rcases p1723_3 (m.d 2 3) (by simp) with h1746 | h1746
              · linarith only [h1525, h1746, hlam]
              · rcases p1723_3 (m.d 2 4) (by simp) with h1748 | h1748
                · linarith only [h1526, h1748, hlam]
                · rcases p1723_3 (m.d 2 5) (by simp) with h1750 | h1750
                  · linarith only [h1750, hlam, p1723_0]
                  · rcases h2emax with h1752 | h1752 | h1752 | h1752 | h1752
                    · linarith only [h1525, h1528, h1530, h1721, h1752, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h1752, hlam, ht12, u1ehi1]
                    · rcases h4bigk with h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1521, hlam, p1755_1]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        rcases p1755_3 (m.d 0 4) (by simp) with h1758 | h1758
                        · rcases p1755_3 (m.d 1 4) (by simp) with h1759 | h1759
                          · rcases p1755_3 (m.d 2 4) (by simp) with h1760 | h1760
                            · linarith only [h1526, h1760, hlam]
                            · rcases p1755_3 (m.d 3 4) (by simp) with h1762 | h1762
                              · linarith only [h1528, h1762, hlam]
                              · rcases p1755_3 (m.d 4 5) (by simp) with h1764 | h1764
                                · linarith only [h1530, h1764, hlam]
                                · linarith only [h1719, h1764, hlam]
                          · linarith only [h1532, h1759, hlam]
                        · linarith only [h1526, h1758, hlam]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1530, h1537, h1538, h1721, hlam, p1755_2]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1525, h1528, h1537, h1538, h1721, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1755_1]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1521, hc14, hlam, hphi, p1755_1, u1ehi0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        rcases p1755_3 (m.d 0 4) (by simp) with h1773 | h1773
                        · linarith only [h1521, h1773, hlam]
                        · linarith only [h1526, h1773, hlam]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1521, h1530, h1537, h1538, h1721, hlam, p1755_2]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1537, h1538, h1721, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1755_1]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1526, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1532, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1530, h1537, h1538, h1721, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1755_1]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1719, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1528, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1534, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1537, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1721, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1530, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [h1536, hlam, p1755_0]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        rcases p1755_3 (m.d 0 4) (by simp) with h1790 | h1790
                        · rcases p1755_3 (m.d 1 4) (by simp) with h1791 | h1791
                          · rcases p1755_3 (m.d 2 4) (by simp) with h1792 | h1792
                            · linarith only [h1792, hlam, p1755_0]
                            · rcases p1755_3 (m.d 3 4) (by simp) with h1794 | h1794
                              · linarith only [h1721, h1794, hlam]
                              · rcases p1755_3 (m.d 4 5) (by simp) with h1796 | h1796
                                · rcases h5bigk with h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [hlam, p1797_0]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1523, hlam, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    rcases p1797_3 (m.d 0 5) (by simp) with h1800 | h1800
                                    · rcases p1797_3 (m.d 1 5) (by simp) with h1801 | h1801
                                      · rcases p1797_3 (m.d 2 5) (by simp) with h1802 | h1802
                                        · linarith only [h1527, h1802, hlam]
                                        · rcases p1797_3 (m.d 3 5) (by simp) with h1804 | h1804
                                          · linarith only [h1529, h1804, hlam]
                                          · linarith only [h1538, h1804, hlam]
                                      · linarith only [h1533, h1801, hlam]
                                    · linarith only [h1527, h1800, hlam]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1521, h1530, h1531, h1534, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1521, h1530, h1531, h1534, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1755_1, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1523, hc15, hlam, hphi, p1797_1, u1ehi0]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [hlam, p1797_0]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    rcases p1797_3 (m.d 0 5) (by simp) with h1813 | h1813
                                    · linarith only [h1523, h1813, hlam]
                                    · linarith only [h1527, h1813, hlam]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1531, h1534, h1536, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1531, h1534, h1536, h1537, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1755_1, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1527, hlam, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1533, hlam, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [hlam, p1797_0]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1538, hlam, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1719, hlam, p1797_0]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1529, hlam, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1535, hlam, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h0, h1525, h1529, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [hlam, p1797_0]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1721, hlam, p1797_0]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1530, hlam, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1536, hlam, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1537, h1538, hc34, hc45, hlam, hphi, p1797_1]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [h1521, h1530, h1531, h1534, hc12, hlam, hphi, ht01, ht0b, ht5b, p1797_1, u5ehi3]
                                  · have p1797_0 := h1797c.1
                                    have p1797_1 := h1797c.2.1
                                    have p1797_2 := h1797c.2.2.1
                                    have p1797_3 := h1797c.2.2.2
                                    linarith only [hlam, p1797_0]
                                · linarith only [h1796, hlam, p1755_0]
                          · linarith only [h1532, h1791, hlam]
                        · linarith only [h1526, h1790, hlam]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        rcases p1755_3 (m.d 0 4) (by simp) with h1836 | h1836
                        · rcases p1755_3 (m.d 1 4) (by simp) with h1837 | h1837
                          · rcases p1755_3 (m.d 2 4) (by simp) with h1838 | h1838
                            · linarith only [h1719, h1838, hlam]
                            · linarith only [h1537, h1838, hlam]
                          · linarith only [h1534, h1837, hlam]
                        · linarith only [h1528, h1836, hlam]
                      · have p1755_0 := h1755c.1
                        have p1755_1 := h1755c.2.1
                        have p1755_2 := h1755c.2.2.1
                        have p1755_3 := h1755c.2.2.2
                        linarith only [hlam, p1755_0]
                    · rcases h4bigk with h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1521, hlam, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 4) (by simp) with h1847 | h1847
                        · rcases p1844_3 (m.d 1 4) (by simp) with h1848 | h1848
                          · rcases p1844_3 (m.d 2 4) (by simp) with h1849 | h1849
                            · linarith only [h1526, h1849, hlam]
                            · rcases p1844_3 (m.d 3 4) (by simp) with h1851 | h1851
                              · linarith only [h1528, h1851, hlam]
                              · rcases p1844_3 (m.d 4 5) (by simp) with h1853 | h1853
                                · linarith only [h1530, h1853, hlam]
                                · linarith only [h1719, h1853, hlam]
                          · linarith only [h1532, h1848, hlam]
                        · linarith only [h1526, h1847, hlam]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1530, h1537, h1538, h1721, hlam, p1844_2]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1521, h1531, h1534, h1537, h1538, h1721, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p1844_1, u1ehi0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 4) (by simp) with h1862 | h1862
                        · linarith only [h1521, h1862, hlam]
                        · linarith only [h1526, h1862, hlam]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1521, h1530, h1537, h1538, h1721, hlam, p1844_2]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1537, h1538, h1721, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1526, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1532, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1530, h1537, h1538, h1721, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1844_1]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1719, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1528, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1534, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1537, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1721, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1530, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [h1536, hlam, p1844_0]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 4) (by simp) with h1879 | h1879
                        · rcases p1844_3 (m.d 1 4) (by simp) with h1880 | h1880
                          · rcases p1844_3 (m.d 2 4) (by simp) with h1881 | h1881
                            · linarith only [h1881, hlam, p1844_0]
                            · rcases p1844_3 (m.d 3 4) (by simp) with h1883 | h1883
                              · linarith only [h1721, h1883, hlam]
                              · rcases p1844_3 (m.d 4 5) (by simp) with h1885 | h1885
                                · rcases h5bigk with h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c | h1886c
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [hlam, p1886_0]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1523, hlam, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    rcases p1886_3 (m.d 0 5) (by simp) with h1889 | h1889
                                    · rcases p1886_3 (m.d 1 5) (by simp) with h1890 | h1890
                                      · rcases p1886_3 (m.d 2 5) (by simp) with h1891 | h1891
                                        · linarith only [h1527, h1891, hlam]
                                        · rcases p1886_3 (m.d 3 5) (by simp) with h1893 | h1893
                                          · linarith only [h1529, h1893, hlam]
                                          · linarith only [h1538, h1893, hlam]
                                      · linarith only [h1533, h1890, hlam]
                                    · linarith only [h1527, h1889, hlam]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1523, h1531, h1534, h1536, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1523, h1531, h1534, h1536, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1844_1, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1523, h1531, h1534, h1536, hc12, hlam, hphi, p1886_1, u1ehi0]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [hlam, p1886_0]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    rcases p1886_3 (m.d 0 5) (by simp) with h1902 | h1902
                                    · linarith only [h1523, h1902, hlam]
                                    · linarith only [h1527, h1902, hlam]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1531, h1534, h1536, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1531, h1534, h1536, h1537, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1844_1, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1527, hlam, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1533, hlam, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [hlam, p1886_0]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1538, hlam, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1719, hlam, p1886_0]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1529, hlam, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1535, hlam, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h0, h1525, h1529, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [hlam, p1886_0]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1721, hlam, p1886_0]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1530, hlam, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1536, hlam, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1537, h1538, hc34, hc45, hlam, hphi, p1886_1]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [h1521, h1530, h1531, h1534, hc12, hlam, hphi, ht01, ht0b, ht5b, p1886_1, u5ehi3]
                                  · have p1886_0 := h1886c.1
                                    have p1886_1 := h1886c.2.1
                                    have p1886_2 := h1886c.2.2.1
                                    have p1886_3 := h1886c.2.2.2
                                    linarith only [hlam, p1886_0]
                                · linarith only [h1885, hlam, p1844_0]
                          · linarith only [h1532, h1880, hlam]
                        · linarith only [h1526, h1879, hlam]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        rcases p1844_3 (m.d 0 4) (by simp) with h1925 | h1925
                        · rcases p1844_3 (m.d 1 4) (by simp) with h1926 | h1926
                          · rcases p1844_3 (m.d 2 4) (by simp) with h1927 | h1927
                            · linarith only [h1719, h1927, hlam]
                            · linarith only [h1537, h1927, hlam]
                          · linarith only [h1534, h1926, hlam]
                        · linarith only [h1528, h1925, hlam]
                      · have p1844_0 := h1844c.1
                        have p1844_1 := h1844c.2.1
                        have p1844_2 := h1844c.2.2.1
                        have p1844_3 := h1844c.2.2.2
                        linarith only [hlam, p1844_0]
                    · rcases h4bigk with h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1521, hlam, p1933_1]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        rcases p1933_3 (m.d 0 4) (by simp) with h1936 | h1936
                        · rcases p1933_3 (m.d 1 4) (by simp) with h1937 | h1937
                          · rcases p1933_3 (m.d 2 4) (by simp) with h1938 | h1938
                            · linarith only [h1526, h1938, hlam]
                            · rcases p1933_3 (m.d 3 4) (by simp) with h1940 | h1940
                              · linarith only [h1528, h1940, hlam]
                              · rcases p1933_3 (m.d 4 5) (by simp) with h1942 | h1942
                                · linarith only [h1530, h1942, hlam]
                                · linarith only [h1719, h1942, hlam]
                          · linarith only [h1532, h1937, hlam]
                        · linarith only [h1526, h1936, hlam]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1530, h1537, h1538, h1721, hlam, p1933_2]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1537, h1538, h1721, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1933_1]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p1933_1, u1ehi0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        rcases p1933_3 (m.d 0 4) (by simp) with h1951 | h1951
                        · linarith only [h1521, h1951, hlam]
                        · linarith only [h1526, h1951, hlam]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1521, h1530, h1537, h1538, h1721, hlam, p1933_2]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1537, h1538, h1721, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1933_1]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1526, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1532, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1530, h1537, h1538, h1721, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1933_1]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1719, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1528, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1534, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1537, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1721, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1530, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [h1536, hlam, p1933_0]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        rcases p1933_3 (m.d 0 4) (by simp) with h1968 | h1968
                        · rcases p1933_3 (m.d 1 4) (by simp) with h1969 | h1969
                          · rcases p1933_3 (m.d 2 4) (by simp) with h1970 | h1970
                            · linarith only [h1970, hlam, p1933_0]
                            · rcases p1933_3 (m.d 3 4) (by simp) with h1972 | h1972
                              · linarith only [h1721, h1972, hlam]
                              · rcases p1933_3 (m.d 4 5) (by simp) with h1974 | h1974
                                · rcases h5bigk with h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [hlam, p1975_0]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1523, hlam, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    rcases p1975_3 (m.d 0 5) (by simp) with h1978 | h1978
                                    · rcases p1975_3 (m.d 1 5) (by simp) with h1979 | h1979
                                      · rcases p1975_3 (m.d 2 5) (by simp) with h1980 | h1980
                                        · linarith only [h1527, h1980, hlam]
                                        · rcases p1975_3 (m.d 3 5) (by simp) with h1982 | h1982
                                          · linarith only [h1529, h1982, hlam]
                                          · linarith only [h1538, h1982, hlam]
                                      · linarith only [h1533, h1979, hlam]
                                    · linarith only [h1527, h1978, hlam]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1523, h1531, h1534, h1536, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1523, h1531, h1534, h1536, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1933_1, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1523, h1531, h1534, h1536, hc12, hlam, hphi, p1975_1, u1ehi0]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [hlam, p1975_0]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    rcases p1975_3 (m.d 0 5) (by simp) with h1991 | h1991
                                    · linarith only [h1523, h1991, hlam]
                                    · linarith only [h1527, h1991, hlam]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1531, h1534, h1536, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1531, h1534, h1536, h1537, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1933_1, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1527, hlam, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1533, hlam, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [hlam, p1975_0]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1538, hlam, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1719, hlam, p1975_0]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1529, hlam, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1535, hlam, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h0, h1525, h1529, h1537, h1538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [hlam, p1975_0]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1721, hlam, p1975_0]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1530, hlam, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1536, hlam, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1537, h1538, hc34, hc45, hlam, hphi, p1975_1]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [h1521, h1530, h1531, h1534, hc12, hlam, hphi, ht01, ht0b, ht5b, p1975_1, u5ehi3]
                                  · have p1975_0 := h1975c.1
                                    have p1975_1 := h1975c.2.1
                                    have p1975_2 := h1975c.2.2.1
                                    have p1975_3 := h1975c.2.2.2
                                    linarith only [hlam, p1975_0]
                                · linarith only [h1974, hlam, p1933_0]
                          · linarith only [h1532, h1969, hlam]
                        · linarith only [h1526, h1968, hlam]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        rcases p1933_3 (m.d 0 4) (by simp) with h2014 | h2014
                        · rcases p1933_3 (m.d 1 4) (by simp) with h2015 | h2015
                          · rcases p1933_3 (m.d 2 4) (by simp) with h2016 | h2016
                            · linarith only [h1719, h2016, hlam]
                            · linarith only [h1537, h2016, hlam]
                          · linarith only [h1534, h2015, hlam]
                        · linarith only [h1528, h2014, hlam]
                      · have p1933_0 := h1933c.1
                        have p1933_1 := h1933c.2.1
                        have p1933_2 := h1933c.2.2.1
                        have p1933_3 := h1933c.2.2.2
                        linarith only [hlam, p1933_0]
            · linarith only [h1533, h1745, hlam]
          · linarith only [h1744, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h0, hc12, hlam, hphi, p1723_1, u1ehi0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          rcases p1723_3 (m.d 0 2) (by simp) with h2026 | h2026
          · linarith only [h0, h2026, hlam]
          · linarith only [h1525, h2026, hlam]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          rcases p1723_3 (m.d 0 2) (by simp) with h2029 | h2029
          · linarith only [h0, h2029, hlam]
          · linarith only [h1526, h2029, hlam]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          rcases p1723_3 (m.d 0 2) (by simp) with h2032 | h2032
          · linarith only [h0, h2032, hlam]
          · linarith only [h1527, h2032, hlam]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1525, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1531, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1525, h1529, h1538, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p1723_1]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1538, hlam, p1723_1]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1526, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1532, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1537, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1719, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1527, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h1533, hlam, p1723_0]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [h0, h1527, h1537, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1723_1]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          rcases p1723_3 (m.d 0 2) (by simp) with h2048 | h2048
          · rcases p1723_3 (m.d 1 2) (by simp) with h2049 | h2049
            · rcases p1723_3 (m.d 2 3) (by simp) with h2050 | h2050
              · linarith only [h1538, h2050, hlam]
              · linarith only [h1537, h2050, hlam]
            · linarith only [h1532, h2049, hlam]
          · linarith only [h1526, h2048, hlam]
        · have p1723_0 := h1723c.1
          have p1723_1 := h1723c.2.1
          have p1723_2 := h1723c.2.2.1
          have p1723_3 := h1723c.2.2.2
          linarith only [hlam, p1723_0]

end R2N4
