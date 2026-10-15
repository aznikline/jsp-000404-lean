import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1178 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1482 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1483 | h1483
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1484 | h1484
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1485 | h1485
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1486 | h1486
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1487 | h1487
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1488 | h1488
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1489 | h1489
              · linarith only [h1178, h1482, h1484, h1489, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases h1bigk with h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h0, hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1178, hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1178, h1484, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1491_1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1178, h1484, hc12, hlam, hphi, ht01, ht0b, ht5b, p1491_1, u5ehi1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [hc01, hc12, hlam, hphi, p1491_1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1178, hc01, hc12, hlam, hphi, p1491_1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  rcases p1491_3 (m.d 0 1) (by simp) with h1500 | h1500
                  · linarith only [h0, h1500, hlam]
                  · linarith only [h1482, h1500, hlam]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1488, hc12, hlam, hphi, ht01, ht0b, ht5b, p1491_1, u5ehi3]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1483, h1488, hc13, hlam, hphi, ht01, ht0b, ht5b, p1491_1, u5ehi3]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1484, hlam, p1491_1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  rcases p1491_3 (m.d 0 1) (by simp) with h1507 | h1507
                  · linarith only [h1178, h1507, hlam]
                  · linarith only [h1482, h1507, hlam]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1484, h1488, hc12, hlam, hphi, ht01, ht0b, ht5b, p1491_1, u5ehi3]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1482, hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1485, hlam, p1491_1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1487, hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1489, hlam, p1491_1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1483, hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1486, hlam, p1491_1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1488, hlam, p1491_0]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [h1483, h1485, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1491_1]
                · have p1491_0 := h1491c.1
                  have p1491_1 := h1491c.2.1
                  have p1491_2 := h1491c.2.2.1
                  have p1491_3 := h1491c.2.2.2
                  linarith only [hlam, p1491_0]
            · linarith only [h1178, h1483, h1488, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
          · linarith only [h1178, h1483, h1486, h1487, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · linarith only [h1178, h1483, h1484, h1486, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
      · linarith only [h1178, h1483, h1484, h1485, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
    · linarith only [h0, h1483, h1484, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1526 | h1526
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1527 | h1527
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1528 | h1528
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1529 | h1529
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1530 | h1530
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1531 | h1531
              · linarith only [h1482, h1483, h1526, h1530, h1531, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases h1bigk with h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h0, hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1178, hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1483, h1531, hc14, hc45, hlam, hphi, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1483, hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [hc01, hc12, hlam, hphi, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1178, h1482, h1527, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  rcases p1533_3 (m.d 0 1) (by simp) with h1542 | h1542
                  · linarith only [h0, h1542, hlam]
                  · linarith only [h1482, h1542, hlam]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1482, h1483, h1527, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1482, h1527, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1526, hlam, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  rcases p1533_3 (m.d 0 1) (by simp) with h1549 | h1549
                  · linarith only [h1178, h1549, hlam]
                  · linarith only [h1482, h1549, hlam]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1482, h1483, h1526, h1527, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1482, hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1527, hlam, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1529, hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1531, hlam, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1482, h1527, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1528, hlam, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1530, hlam, p1533_0]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [h1527, h1531, hc24, hc45, hlam, hphi, p1533_1]
                · have p1533_0 := h1533c.1
                  have p1533_1 := h1533c.2.1
                  have p1533_2 := h1533c.2.2.1
                  have p1533_3 := h1533c.2.2.2
                  linarith only [hlam, p1533_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1563 | h1563
              · linarith only [h0, h1482, h1563, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
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
                  linarith only [h0, hlam, p1565_0]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1178, hlam, p1565_0]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1178, h1530, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1483, hlam, p1565_0]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [hc01, hc12, hlam, hphi, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [hlam, p1565_0]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1178, h1482, h1527, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  rcases p1565_3 (m.d 0 1) (by simp) with h1574 | h1574
                  · linarith only [h0, h1574, hlam]
                  · linarith only [h1482, h1574, hlam]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1565_1, u5ehi1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1482, h1527, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1526, hlam, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [hlam, p1565_0]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1527, h1530, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1530, hlam, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1482, hlam, p1565_0]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1527, hlam, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1529, hlam, p1565_0]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [hlam, p1565_0]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1563, hlam, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1482, h1527, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1528, hlam, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1563, hc13, hc45, hlam, hphi, ht34, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [h1527, h1563, hc24, hc45, hlam, hphi, p1565_1]
                · have p1565_0 := h1565c.1
                  have p1565_1 := h1565c.2.1
                  have p1565_2 := h1565c.2.2.1
                  have p1565_3 := h1565c.2.2.2
                  linarith only [hlam, p1565_0]
          · linarith only [h1178, h1482, h1529, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1594 | h1594
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1595 | h1595
            · linarith only [h1526, h1528, h1595, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1597 | h1597
              · linarith only [h0, h1482, h1528, h1597, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases h1bigk with h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h0, hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1178, hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1178, h1526, h1528, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1483, hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1528, hc01, hc25, hlam, hphi, ht12, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1528, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1527, h1528, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1528, hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1482, h1527, h1595, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1526, hlam, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1527, h1595, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1595, hlam, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1482, hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1527, hlam, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1594, hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [hlam, p1599_0]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1597, hlam, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1482, h1527, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1597, hc12, hc45, hlam, hphi, ht23, ht34, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1178, h1482, h1527, h1597, hc24, hc45, hlam, hphi, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [h1527, h1597, hc24, hc45, hlam, hphi, p1599_1]
                · have p1599_0 := h1599c.1
                  have p1599_1 := h1599c.2.1
                  have p1599_2 := h1599c.2.2.1
                  have p1599_3 := h1599c.2.2.2
                  linarith only [hlam, p1599_0]
          · linarith only [h1178, h1482, h1594, hlam]
      · linarith only [h1178, h1482, h1526, h1527, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1627 | h1627
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1628 | h1628
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1629 | h1629
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1630 | h1630
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1631 | h1631
              · linarith only [h1482, h1483, h1628, h1631, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases h1bigk with h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h0, hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1178, hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1483, h1526, h1627, h1628, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1483, hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1526, hc01, hc23, hlam, hphi, ht12, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1526, hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1526, h1627, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1526, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1633_1, u5ehi1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1482, h1526, h1627, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1526, hc12, hc23, hlam, hphi, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  rcases p1633_3 (m.d 0 1) (by simp) with h1647 | h1647
                  · linarith only [h1178, h1647, hlam]
                  · linarith only [h1482, h1647, hlam]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1482, h1483, h1526, h1627, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1482, hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1627, hlam, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1629, hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1631, hlam, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1482, h1627, h1628, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1628, hlam, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1630, hlam, p1633_0]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [h1526, h1627, h1628, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1633_1]
                · have p1633_0 := h1633c.1
                  have p1633_1 := h1633c.2.1
                  have p1633_2 := h1633c.2.2.1
                  have p1633_3 := h1633c.2.2.2
                  linarith only [hlam, p1633_0]
            · linarith only [h1526, h1628, h1630, hlam]
          · linarith only [h0, h1482, h1526, h1629, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1663 | h1663
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1664 | h1664
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1665 | h1665
              · linarith only [h0, h1482, h1526, h1665, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases h1bigk with h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h0, hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1178, hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h0, h1526, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1483, hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1526, hc01, hc23, hlam, hphi, ht12, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1526, hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1526, h1627, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1628, hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1482, h1627, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1526, hc12, hc23, hlam, hphi, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  rcases p1667_3 (m.d 0 1) (by simp) with h1681 | h1681
                  · linarith only [h1178, h1681, hlam]
                  · linarith only [h1482, h1681, hlam]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h0, h1482, h1526, h1627, h1628, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1482, hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1627, hlam, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1663, hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1665, hlam, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1482, h1627, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h0, h1482, h1627, h1665, hc24, hc45, hlam, hphi, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1664, hlam, p1667_0]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [h1627, h1665, hc24, hc45, hlam, hphi, p1667_1]
                · have p1667_0 := h1667c.1
                  have p1667_1 := h1667c.2.1
                  have p1667_2 := h1667c.2.2.1
                  have p1667_3 := h1667c.2.2.2
                  linarith only [hlam, p1667_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1695 | h1695
              · linarith only [h0, h1482, h1695, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases h1bigk with h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h0, hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1178, hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h0, h1526, h1664, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1483, hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1526, h1664, hc01, hc35, hlam, hphi, ht12, ht23, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1526, hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1526, h1627, h1664, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1628, hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1482, h1627, h1664, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1664, hc12, hc35, hlam, hphi, ht23, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1627, h1664, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1664, hlam, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1482, hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1627, hlam, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1663, hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [hlam, p1697_0]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1695, hlam, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1482, h1627, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h0, h1482, h1627, h1695, hc24, hc45, hlam, hphi, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1695, hc13, hc45, hlam, hphi, ht34, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [h1627, h1695, hc24, hc45, hlam, hphi, p1697_1]
                · have p1697_0 := h1697c.1
                  have p1697_1 := h1697c.2.1
                  have p1697_2 := h1697c.2.2.1
                  have p1697_3 := h1697c.2.2.2
                  linarith only [hlam, p1697_0]
          · linarith only [h0, h1482, h1526, h1663, hlam]
      · linarith only [h0, h1482, h1627, hlam]

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1178 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1482 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1725 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1726 | h1726
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1727 | h1727
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1728 | h1728
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1729 | h1729
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1730 | h1730
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1731 | h1731
            · rcases h1bigk with h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c | h1732c
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h0, hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1178, hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1482, hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1728, hc01, hlam, hphi, ht0b, ht5b, p1732_1, u5ehi2]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [hc01, hc12, hlam, hphi, p1732_1]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1729, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1732_1]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1482, h1725, h1728, hc12, hlam, hphi, ht01, ht0b, ht5b, p1732_1, u5ehi2]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1728, hc12, hlam, hphi, ht01, ht0b, ht5b, p1732_1, u5ehi2]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1725, h1728, hc13, hlam, hphi, ht01, ht0b, ht5b, p1732_1, u5ehi2]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1726, hlam, p1732_1]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1482, h1725, h1726, h1728, hc12, hlam, hphi, ht01, ht0b, ht5b, p1732_1, u5ehi2]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1726, h1728, hc12, hlam, hphi, ht01, ht0b, ht5b, p1732_1, u5ehi2]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1725, h1728, hc14, hlam, hphi, ht01, ht0b, ht5b, p1732_1, u5ehi2]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1727, hlam, p1732_1]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1729, hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1726, h1728, h1729, hc12, hlam, hphi, ht01, ht0b, ht5b, p1732_1, u5ehi2]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1725, hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1728, hlam, p1732_1]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1730, hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [h1731, hlam, p1732_0]
              · have p1732_0 := h1732c.1
                have p1732_1 := h1732c.2.1
                have p1732_2 := h1732c.2.2.1
                have p1732_3 := h1732c.2.2.2
                linarith only [hlam, p1732_0]
            · linarith only [h1482, h1725, h1728, h1731, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
          · linarith only [h1178, h1725, h1728, h1730, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · linarith only [h1178, h1725, h1728, h1729, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
      · linarith only [h0, h1725, h1728, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
    · linarith only [h1178, h1725, h1726, h1727, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
  · linarith only [h0, h1725, h1726, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]

end R2N4
