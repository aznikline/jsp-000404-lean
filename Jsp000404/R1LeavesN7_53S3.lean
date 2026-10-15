import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1562 | h1562
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1563 | h1563
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1564 | h1564
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1565 | h1565
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1566 | h1566
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1567 | h1567
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1568 | h1568
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1569 | h1569
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1570 | h1570
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1571 | h1571
                    · rcases h0emax with h1572 | h1572 | h1572 | h1572 | h1572
                      · rcases h5bigk with h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h674, hlam, p1573_1]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1557, hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1559, h1561, h1562, h855, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1573_1]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1559, h1561, h1562, h855, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1573_1]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1565, h1567, h674, hc01, hc13, hlam, hphi, p1573_1]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1557, h1562, h1565, h1567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1573_1, u2ehi0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1562, h1565, h1567, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1573_1, u3ehi4]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          rcases p1573_3 (m.d 0 5) (by simp) with h1583 | h1583
                          · linarith only [h1583, h674, hlam]
                          · linarith only [h1561, h1583, hlam]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p1573_1, u2ehi0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1564, hlam, p1573_1]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1562, h1569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1573_1, u3ehi4]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1562, h1568, h1570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1573_1]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1560, hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1566, hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1569, hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1560, h1562, h855, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1573_1]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1561, hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1567, hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1570, hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [h1571, hlam, p1573_0]
                        · have p1573_0 := h1573c.1
                          have p1573_1 := h1573c.2.1
                          have p1573_2 := h1573c.2.2.1
                          have p1573_3 := h1573c.2.2.2
                          linarith only [hlam, p1573_0]
                      · rcases h5bigk with h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h674, hlam, p1601_1]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1557, hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1601_1, u3ehi4]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1557, h1562, h1568, h1570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1601_1]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1562, h1565, h1567, h674, hc01, hc12, hlam, hphi, p1601_1]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1562, h1565, h1567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1601_1, u2ehi4]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1562, h1565, h1567, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1601_1, u3ehi4]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          rcases p1601_3 (m.d 0 5) (by simp) with h1611 | h1611
                          · linarith only [h1611, h674, hlam]
                          · linarith only [h1561, h1611, hlam]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p1601_1, u2ehi0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1564, hlam, p1601_1]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1562, h1569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1601_1, u3ehi4]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1562, h1568, h1570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1601_1]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1560, hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1566, hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1569, hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1560, h1562, h855, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1601_1]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1561, hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1567, hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1570, hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [h1571, hlam, p1601_0]
                        · have p1601_0 := h1601c.1
                          have p1601_1 := h1601c.2.1
                          have p1601_2 := h1601c.2.2.1
                          have p1601_3 := h1601c.2.2.2
                          linarith only [hlam, p1601_0]
                      · linarith only [h1559, h1572, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases h5bigk with h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h674, hlam, p1630_1]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1557, hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1630_1, u3ehi4]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1561, h1572, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1562, h1565, h1567, h674, hc01, hc12, hlam, hphi, p1630_1]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1562, h1565, h1567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1630_1, u2ehi4]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1562, h1565, h1567, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1630_1, u3ehi4]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          rcases p1630_3 (m.d 0 5) (by simp) with h1640 | h1640
                          · linarith only [h1640, h674, hlam]
                          · linarith only [h1561, h1640, hlam]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p1630_1, u2ehi0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1564, hlam, p1630_1]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1562, h1569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1630_1, u3ehi4]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1562, h1568, h1570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1630_1]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1560, hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1566, hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1569, hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1559, h1571, hc03, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1561, hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1567, hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1570, hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [h1571, hlam, p1630_0]
                        · have p1630_0 := h1630c.1
                          have p1630_1 := h1630c.2.1
                          have p1630_2 := h1630c.2.2.1
                          have p1630_3 := h1630c.2.2.2
                          linarith only [hlam, p1630_0]
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
                          linarith only [h674, hlam, p1658_1]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1557, hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi4]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1557, h1562, h1568, h1570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1658_1]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1562, h1565, h1567, h674, hc01, hc12, hlam, hphi, p1658_1]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1562, h1565, h1567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1658_1, u2ehi4]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1562, h1565, h1567, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi4]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          rcases p1658_3 (m.d 0 5) (by simp) with h1668 | h1668
                          · linarith only [h1668, h674, hlam]
                          · linarith only [h1561, h1668, hlam]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p1658_1, u2ehi0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1564, hlam, p1658_1]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1562, h1569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1658_1, u3ehi4]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1562, h1568, h1570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1658_1]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1560, hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1566, hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1569, hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1560, h1562, h855, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1658_1]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1561, hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1567, hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1570, hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [h1571, hlam, p1658_0]
                        · have p1658_0 := h1658c.1
                          have p1658_1 := h1658c.2.1
                          have p1658_2 := h1658c.2.2.1
                          have p1658_3 := h1658c.2.2.2
                          linarith only [hlam, p1658_0]
                    · linarith only [h1559, h1561, h1562, h1571, h855, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1559, h1561, h1562, h1570, h855, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h1560, h1569, h855, hlam]
              · linarith only [h1560, h1568, h855, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1559, h1561, h1562, h1563, h1567, h855, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
          · linarith only [h1560, h1562, h1566, h855, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h1559, h1562, h1565, h855, hlam]
      · linarith only [h1562, h1564, h855, hc25, hlam, hphi, u2ehi0]
    · linarith only [h1562, h1563, h855, hc24, hlam, hphi, u2ehi0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1695 | h1695
    · linarith only [h1562, h1695, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1697 | h1697
      · linarith only [h1562, h1697, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1699 | h1699
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1700 | h1700
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1701 | h1701
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1702 | h1702
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1703 | h1703
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1704 | h1704
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1705 | h1705
                    · rcases h0emax with h1706 | h1706 | h1706 | h1706 | h1706
                      · rcases h5bigk with h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h674, hlam, p1707_1]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1557, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1707_1, u3ehi4]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          rcases p1707_3 (m.d 0 5) (by simp) with h1712 | h1712
                          · rcases p1707_3 (m.d 1 5) (by simp) with h1713 | h1713
                            · rcases p1707_3 (m.d 2 5) (by simp) with h1714 | h1714
                              · rcases p1707_3 (m.d 3 5) (by simp) with h1715 | h1715
                                · linarith only [h1560, h1715, hlam]
                                · linarith only [h1705, h1715, hlam]
                              · linarith only [h1704, h1714, hlam]
                            · linarith only [h1701, h1713, hlam]
                          · linarith only [h1561, h1712, hlam]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1562, h1699, h1701, h674, hc01, hc23, hlam, hphi, ht12, p1707_1]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1697, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1562, h1699, h1701, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1707_1, u3ehi4]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          rcases p1707_3 (m.d 0 5) (by simp) with h1725 | h1725
                          · linarith only [h1725, h674, hlam]
                          · linarith only [h1561, h1725, hlam]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1557, h1702, h1704, hc23, hlam, hphi, p1707_1, u2ehi0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1707_1]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1702, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1707_1, u3ehi4]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          rcases p1707_3 (m.d 0 5) (by simp) with h1732 | h1732
                          · linarith only [h1557, h1732, hlam]
                          · linarith only [h1561, h1732, hlam]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1560, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1700, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1703, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1560, h1562, h482, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1707_1]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1561, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1701, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1704, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [h1705, hlam, p1707_0]
                        · have p1707_0 := h1707c.1
                          have p1707_1 := h1707c.2.1
                          have p1707_2 := h1707c.2.2.1
                          have p1707_3 := h1707c.2.2.2
                          linarith only [hlam, p1707_0]
                      · rcases h5bigk with h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h674, hlam, p1745_1]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1557, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h674, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1745_1, u3ehi4]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          rcases p1745_3 (m.d 0 5) (by simp) with h1750 | h1750
                          · rcases p1745_3 (m.d 1 5) (by simp) with h1751 | h1751
                            · rcases p1745_3 (m.d 2 5) (by simp) with h1752 | h1752
                              · rcases p1745_3 (m.d 3 5) (by simp) with h1753 | h1753
                                · linarith only [h1560, h1753, hlam]
                                · linarith only [h1705, h1753, hlam]
                              · linarith only [h1704, h1752, hlam]
                            · linarith only [h1701, h1751, hlam]
                          · linarith only [h1561, h1750, hlam]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1697, h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1745_1]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1697, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1697, h1702, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1745_1, u3ehi4]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          rcases p1745_3 (m.d 0 5) (by simp) with h1763 | h1763
                          · linarith only [h1763, h674, hlam]
                          · linarith only [h1561, h1763, hlam]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1557, h1702, h1704, hc23, hlam, hphi, p1745_1, u2ehi0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1745_1]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1702, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1745_1, u3ehi4]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          rcases p1745_3 (m.d 0 5) (by simp) with h1770 | h1770
                          · linarith only [h1557, h1770, hlam]
                          · linarith only [h1561, h1770, hlam]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1560, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1700, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1703, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1560, h1562, h482, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1745_1]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1561, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1701, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1704, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [h1705, hlam, p1745_0]
                        · have p1745_0 := h1745c.1
                          have p1745_1 := h1745c.2.1
                          have p1745_2 := h1745c.2.2.1
                          have p1745_3 := h1745c.2.2.2
                          linarith only [hlam, p1745_0]
                      · linarith only [h1559, h1706, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases h5bigk with h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c | h1784c
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h674, hlam, p1784_1]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1557, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1784_1, u3ehi4]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1561, h1706, hc45, hlam, hphi, ht0b, ht5b, p1784_1]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p1784_1]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1697, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1700, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1784_1, u3ehi4]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          rcases p1784_3 (m.d 0 5) (by simp) with h1794 | h1794
                          · linarith only [h1794, h674, hlam]
                          · linarith only [h1561, h1794, hlam]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1557, h1702, h1704, hc23, hlam, hphi, p1784_1, u2ehi0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1784_1]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1557, h1561, h1702, h1704, h1706, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1784_1, u2ehi0, u3ehi4]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          rcases p1784_3 (m.d 0 5) (by simp) with h1801 | h1801
                          · linarith only [h1557, h1801, hlam]
                          · linarith only [h1561, h1801, hlam]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1560, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1700, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1703, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1559, h1705, hc03, hc45, hlam, hphi, ht0b, ht5b, p1784_1]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1561, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1701, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1704, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [h1705, hlam, p1784_0]
                        · have p1784_0 := h1784c.1
                          have p1784_1 := h1784c.2.1
                          have p1784_2 := h1784c.2.2.1
                          have p1784_3 := h1784c.2.2.2
                          linarith only [hlam, p1784_0]
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
                          linarith only [h674, hlam, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1557, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1814_1, u3ehi4]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1706, hc45, hlam, hphi, ht0b, ht5b, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1697, h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1697, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1697, h1702, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1814_1, u3ehi4]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          rcases p1814_3 (m.d 0 5) (by simp) with h1824 | h1824
                          · linarith only [h1824, h674, hlam]
                          · linarith only [h1561, h1824, hlam]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1557, h1702, h1704, hc23, hlam, hphi, p1814_1, u2ehi0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1702, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1814_1, u3ehi4]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          rcases p1814_3 (m.d 0 5) (by simp) with h1831 | h1831
                          · linarith only [h1557, h1831, hlam]
                          · linarith only [h1561, h1831, hlam]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1560, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1700, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1703, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1560, h1562, h482, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1814_1]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1561, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1701, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1704, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [h1705, hlam, p1814_0]
                        · have p1814_0 := h1814c.1
                          have p1814_1 := h1814c.2.1
                          have p1814_2 := h1814c.2.2.1
                          have p1814_3 := h1814c.2.2.2
                          linarith only [hlam, p1814_0]
                    · rcases h0emax with h1844 | h1844 | h1844 | h1844 | h1844
                      · rcases h5bigk with h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h674, hlam, p1845_1]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1557, hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1845_1, u3ehi4]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1559, h1561, h1562, h1705, h482, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1845_1]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p1845_1]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1697, hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1697, h1702, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1845_1, u3ehi4]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1697, h1702, h1704, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1845_1, u3ehi3]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1561, h1702, h1704, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1845_1, u3ehi3]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1845_1]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1702, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1845_1, u3ehi4]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1702, h1704, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1845_1, u3ehi3]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1560, hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1700, hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1703, hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1705, hlam, p1845_1]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1561, hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1701, hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1704, hlam, p1845_0]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [h1561, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1845_1, u3ehi4]
                        · have p1845_0 := h1845c.1
                          have p1845_1 := h1845c.2.1
                          have p1845_2 := h1845c.2.2.1
                          have p1845_3 := h1845c.2.2.2
                          linarith only [hlam, p1845_0]
                      · rcases h5bigk with h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c | h1871c
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h674, hlam, p1871_1]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1557, hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1559, h1561, h1562, h1705, h482, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1871_1, u3ehi3]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1559, h1561, h1562, h1705, h482, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1871_1, u3ehi3]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1697, h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1871_1]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1697, hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1697, h1702, h1704, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1871_1, u3ehi3]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1697, h1702, h1704, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1871_1, u3ehi3]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1561, h1702, h1704, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1871_1, u3ehi3]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1702, h1704, h674, hc01, hc23, hlam, hphi, ht12, p1871_1]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1702, h1704, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1871_1, u3ehi3]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1702, h1704, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1871_1, u3ehi3]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1560, hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1700, hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1703, hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1705, hlam, p1871_1]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1561, hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1701, hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1704, hlam, p1871_0]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [h1561, h1705, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1871_1, u3ehi3]
                        · have p1871_0 := h1871c.1
                          have p1871_1 := h1871c.2.1
                          have p1871_2 := h1871c.2.2.1
                          have p1871_3 := h1871c.2.2.2
                          linarith only [hlam, p1871_0]
                      · linarith only [h1559, h1844, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1561, h1705, h1844, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1561, h1705, h1844, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1559, h1561, h1562, h1704, h482, hc23, hlam, hphi, u2ehi3]
                · linarith only [h1703, h855, hc35, hlam, hphi, ht23, u2ehi0]
              · linarith only [h0, h1559, h1562, h1702, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h0, h1559, h1561, h1562, h1695, h1701, h482, hc01, hc23, hlam, hphi, ht12]
          · linarith only [h1560, h1700, h482, hlam]
        · linarith only [h1559, h1699, h482, hlam]

end R2N4
