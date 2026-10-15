import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1255 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1522 | h1522
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1523 | h1523
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1524 | h1524
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1525 | h1525
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1526 | h1526
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1527 | h1527
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1528 | h1528
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1529 | h1529
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1530 | h1530
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1531 | h1531
                    · rcases h1bigk with h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h0, hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1255, hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1524, h1529, h1531, hc01, hc45, hlam, hphi, ht0b, ht5b, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1255, h1523, h1525, h1530, h1531, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1255, hc01, hc12, hlam, hphi, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1524, h1529, h1531, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        rcases p1532_3 (m.d 0 1) (by simp) with h1542 | h1542
                        · linarith only [h0, h1542, hlam]
                        · linarith only [h1522, h1542, hlam]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1521, h1524, h1529, h1531, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1523, hlam, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1523, h1524, h1529, h1531, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        rcases p1532_3 (m.d 0 1) (by simp) with h1549 | h1549
                        · linarith only [h1255, h1549, hlam]
                        · linarith only [h1522, h1549, hlam]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1521, hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1524, hlam, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1526, hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1521, h1525, h1530, h1531, hc01, hc45, hlam, hphi, ht0b, ht5b, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1522, hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1525, hlam, p1532_1]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1527, hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [h1528, hlam, p1532_0]
                      · have p1532_0 := h1532c.1
                        have p1532_1 := h1532c.2.1
                        have p1532_2 := h1532c.2.2.1
                        have p1532_3 := h1532c.2.2.2
                        linarith only [hlam, p1532_0]
                    · linarith only [h1255, h1521, h1523, h1528, h1531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h1529, h1530, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1564 | h1564
                  · linarith only [h1255, h1521, h1523, h1526, h1529, h1564, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1566 | h1566
                    · rcases h1bigk with h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h0, hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1255, hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1255, h1523, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1255, h1523, h1527, h1564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1255, hc01, hc12, hlam, hphi, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1527, h1528, h1564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1527, h1564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1521, h1527, h1528, h1564, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1523, hlam, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1523, h1527, h1528, h1564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1523, h1527, h1564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1521, hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1524, hlam, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1526, hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1521, h1527, h1564, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1522, hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1525, hlam, p1567_1]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1527, hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [h1528, hlam, p1567_0]
                      · have p1567_0 := h1567c.1
                        have p1567_1 := h1567c.2.1
                        have p1567_2 := h1567c.2.2.1
                        have p1567_3 := h1567c.2.2.2
                        linarith only [hlam, p1567_0]
                    · linarith only [h1255, h1521, h1523, h1528, h1566, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1594 | h1594
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1595 | h1595
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1596 | h1596
                    · linarith only [h1526, h1528, h1596, hlam]
                    · rcases h1bigk with h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h0, hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1255, hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1255, h1523, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1255, h1523, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1255, hc01, hc12, hlam, hphi, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        rcases p1598_3 (m.d 0 1) (by simp) with h1607 | h1607
                        · linarith only [h0, h1607, hlam]
                        · linarith only [h1521, h1607, hlam]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        rcases p1598_3 (m.d 0 1) (by simp) with h1610 | h1610
                        · linarith only [h0, h1610, hlam]
                        · linarith only [h1522, h1610, hlam]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1522, h1524, h1528, h1594, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1523, hlam, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        rcases p1598_3 (m.d 0 1) (by simp) with h1616 | h1616
                        · linarith only [h1255, h1616, hlam]
                        · linarith only [h1521, h1616, hlam]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        rcases p1598_3 (m.d 0 1) (by simp) with h1619 | h1619
                        · linarith only [h1255, h1619, hlam]
                        · linarith only [h1522, h1619, hlam]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1521, hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1524, hlam, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1526, hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1528, hlam, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1522, hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1525, hlam, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1527, hlam, p1598_0]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [h1522, h1524, h1594, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1598_1]
                      · have p1598_0 := h1598c.1
                        have p1598_1 := h1598c.2.1
                        have p1598_2 := h1598c.2.2.1
                        have p1598_3 := h1598c.2.2.2
                        linarith only [hlam, p1598_0]
                  · linarith only [h1255, h1522, h1523, h1527, h1594, h1595, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h1526, h1528, h1594, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h1255, h1527, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h1255, h1521, h1526, hlam]
        · linarith only [h0, h1521, h1524, h1525, hc24, hlam, hphi, ht45, u5elo2]
      · linarith only [h1255, h1521, h1523, h1524, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1638 | h1638
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1639 | h1639
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1640 | h1640
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1641 | h1641
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1642 | h1642
              · linarith only [h0, h1521, h1523, h1642, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1644 | h1644
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1645 | h1645
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1646 | h1646
                    · linarith only [h1638, h1642, h1644, h1646, hlam]
                    · rcases h1bigk with h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h0, hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1255, hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h0, h1523, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h0, h1523, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1523, hc01, hc23, hlam, hphi, ht12, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1523, hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1523, h1638, h1644, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1523, h1639, h1645, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1521, h1638, h1644, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h0, h1523, hc02, hc23, hlam, hphi, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        rcases p1648_3 (m.d 0 1) (by simp) with h1662 | h1662
                        · linarith only [h1255, h1662, hlam]
                        · linarith only [h1521, h1662, hlam]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        rcases p1648_3 (m.d 0 1) (by simp) with h1665 | h1665
                        · linarith only [h1255, h1665, hlam]
                        · linarith only [h1522, h1665, hlam]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1521, hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1638, hlam, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1640, hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1642, hlam, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1522, hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1639, hlam, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1641, hlam, p1648_0]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [h1522, h1638, h1644, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1648_1]
                      · have p1648_0 := h1648c.1
                        have p1648_1 := h1648c.2.1
                        have p1648_2 := h1648c.2.2.1
                        have p1648_3 := h1648c.2.2.2
                        linarith only [hlam, p1648_0]
                  · linarith only [h0, h1523, h1645, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h1522, h1523, h1638, h1642, h1644, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h1255, h1522, h1641, hc15, hlam, hphi, u5elo3]
          · linarith only [h0, h1521, h1523, h1640, hlam]
        · linarith only [h0, h1521, h1638, h1639, hc24, hlam, hphi, ht45, u5elo2]
      · linarith only [h0, h1521, h1638, hlam]
  · linarith only [h1521, h1522, hc14, hlam, hphi, ht45, u5elo1]

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1255 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1685 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1686 | h1686
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1687 | h1687
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1688 | h1688
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1689 | h1689
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1690 | h1690
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1691 | h1691
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1692 | h1692
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1693 | h1693
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1694 | h1694
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
                      linarith only [h0, hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1255, hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1521, hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1521, h1688, h1689, h1693, h1694, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1255, h1685, h1688, h1693, h1694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1521, h1685, h1688, h1693, h1694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      rcases p1695_3 (m.d 0 1) (by simp) with h1705 | h1705
                      · linarith only [h0, h1705, hlam]
                      · linarith only [h1685, h1705, hlam]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1685, h1688, h1693, h1694, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1686, hlam, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1521, h1685, h1686, h1688, h1693, h1694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      rcases p1695_3 (m.d 0 1) (by simp) with h1712 | h1712
                      · linarith only [h1255, h1712, hlam]
                      · linarith only [h1685, h1712, hlam]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1685, h1688, h1693, h1694, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1687, hlam, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1689, hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      rcases p1695_3 (m.d 0 1) (by simp) with h1719 | h1719
                      · linarith only [h1521, h1719, hlam]
                      · linarith only [h1685, h1719, hlam]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1685, hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1688, hlam, p1695_1]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1690, hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [h1691, hlam, p1695_0]
                    · have p1695_0 := h1695c.1
                      have p1695_1 := h1695c.2.1
                      have p1695_2 := h1695c.2.2.1
                      have p1695_3 := h1695c.2.2.2
                      linarith only [hlam, p1695_0]
                  · rcases h1bigk with h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h0, hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1255, hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1521, hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1691, h1694, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1255, hc01, hc12, hlam, hphi, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1521, h1685, h1691, h1694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1691, h1694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1685, h1691, h1694, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1686, hlam, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1521, h1685, h1686, h1691, h1694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1686, h1691, h1694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1685, h1691, h1694, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1687, hlam, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1689, hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1686, h1689, h1691, h1694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1685, hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1688, hlam, p1727_1]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1690, hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [h1691, hlam, p1727_0]
                    · have p1727_0 := h1727c.1
                      have p1727_1 := h1727c.2.1
                      have p1727_2 := h1727c.2.2.1
                      have p1727_3 := h1727c.2.2.2
                      linarith only [hlam, p1727_0]
                · linarith only [h1692, h1693, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1754 | h1754
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1755 | h1755
                  · rcases h1bigk with h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c | h1756c
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h0, hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1255, hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1521, hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1689, h1692, h1754, h1755, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1521, h1685, h1688, h1754, h1755, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      rcases p1756_3 (m.d 0 1) (by simp) with h1766 | h1766
                      · linarith only [h0, h1766, hlam]
                      · linarith only [h1685, h1766, hlam]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1685, h1688, h1754, h1755, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1686, hlam, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1521, h1685, h1686, h1688, h1754, h1755, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      rcases p1756_3 (m.d 0 1) (by simp) with h1773 | h1773
                      · linarith only [h1255, h1773, hlam]
                      · linarith only [h1685, h1773, hlam]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1685, h1688, h1754, h1755, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1687, hlam, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1689, hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      rcases p1756_3 (m.d 0 1) (by simp) with h1780 | h1780
                      · linarith only [h1521, h1780, hlam]
                      · linarith only [h1685, h1780, hlam]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1685, hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1688, hlam, p1756_1]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1690, hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [h1691, hlam, p1756_0]
                    · have p1756_0 := h1756c.1
                      have p1756_1 := h1756c.2.1
                      have p1756_2 := h1756c.2.2.1
                      have p1756_3 := h1756c.2.2.2
                      linarith only [hlam, p1756_0]
                  · linarith only [h1692, h1755, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1789 | h1789
                  · rcases h1bigk with h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c | h1790c
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h0, hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1255, hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1521, hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1690, h1754, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1255, hc01, hc12, hlam, hphi, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1521, h1685, h1690, h1754, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1690, h1754, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1685, h1690, h1754, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1686, hlam, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1521, h1685, h1686, h1690, h1754, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1686, h1690, h1754, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1685, h1690, h1754, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1687, hlam, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1689, hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1686, h1689, h1690, h1754, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1685, hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1688, hlam, p1790_1]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1690, hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [h1691, hlam, p1790_0]
                    · have p1790_0 := h1790c.1
                      have p1790_1 := h1790c.2.1
                      have p1790_2 := h1790c.2.2.1
                      have p1790_3 := h1790c.2.2.2
                      linarith only [hlam, p1790_0]
                  · linarith only [h1691, h1692, h1789, hc23, hlam, hphi, ht34, ht45, u5elo1]
            · linarith only [h1521, h1691, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h1255, h1685, h1688, h1690, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1819 | h1819
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1820 | h1820
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1821 | h1821
              · linarith only [h1255, h1685, h1688, h1689, h1821, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1823 | h1823
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1824 | h1824
                  · rcases h1bigk with h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h0, hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1255, hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1521, hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1255, h1688, h1823, h1824, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1255, h1685, h1688, h1823, h1824, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1521, h1685, h1688, h1823, h1824, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      rcases p1825_3 (m.d 0 1) (by simp) with h1835 | h1835
                      · linarith only [h0, h1835, hlam]
                      · linarith only [h1685, h1835, hlam]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1685, h1688, h1823, h1824, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1686, hlam, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1689, hlam, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1688, h1689, h1823, h1824, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1685, h1688, h1689, h1823, h1824, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1687, hlam, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1689, hc13, hc34, hlam, hphi, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      rcases p1825_3 (m.d 0 1) (by simp) with h1847 | h1847
                      · linarith only [h1521, h1847, hlam]
                      · linarith only [h1685, h1847, hlam]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1685, hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1688, hlam, p1825_1]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1819, hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [h1820, hlam, p1825_0]
                    · have p1825_0 := h1825c.1
                      have p1825_1 := h1825c.2.1
                      have p1825_2 := h1825c.2.2.1
                      have p1825_3 := h1825c.2.2.2
                      linarith only [hlam, p1825_0]
                  · linarith only [h1521, h1685, h1688, h1689, h1823, h1824, hc35, hlam, hphi, u5elo4]
                · linarith only [h1689, h1819, h1823, hc23, hc34, hlam, hphi]
            · linarith only [h1255, h1689, h1820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h1255, h1685, h1688, h1819, hc25, hlam, hphi, u5elo3]
      · linarith only [h0, h1688, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1860 | h1860
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1861 | h1861
        · linarith only [h1686, h1687, h1861, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1863 | h1863
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1864 | h1864
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1865 | h1865
              · linarith only [h1255, h1685, h1860, h1861, h1865, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1867 | h1867
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1868 | h1868
                  · rcases h1bigk with h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h0, hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1255, hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1521, hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1255, h1686, h1860, h1867, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1687, h1865, hc01, hc34, hlam, hphi, ht12, ht23, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1687, h1865, hc13, hc34, hlam, hphi, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1687, hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1687, h1860, h1865, h1867, h1868, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1685, h1860, h1867, h1868, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1686, hlam, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1861, hlam, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1686, h1687, h1860, h1865, h1867, h1868, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1685, h1860, h1867, h1868, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h0, h1687, h1865, hc02, hc34, hlam, hphi, ht23, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1255, h1685, h1687, h1860, h1865, h1867, h1868, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      rcases p1869_3 (m.d 0 1) (by simp) with h1889 | h1889
                      · linarith only [h1521, h1889, hlam]
                      · linarith only [h1685, h1889, hlam]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1685, hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1860, hlam, p1869_1]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1863, hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [h1864, hlam, p1869_0]
                    · have p1869_0 := h1869c.1
                      have p1869_1 := h1869c.2.1
                      have p1869_2 := h1869c.2.2.1
                      have p1869_3 := h1869c.2.2.2
                      linarith only [hlam, p1869_0]
                  · linarith only [h1521, h1685, h1687, h1860, h1865, h1867, h1868, hc35, hlam, hphi, u5elo4]
                · linarith only [h1686, h1687, h1863, h1865, h1867, hc23, hc34, hlam, hphi]
            · linarith only [h1255, h1686, h1687, h1864, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h1255, h1685, h1860, h1863, hc25, hlam, hphi, u5elo3]
      · linarith only [h1255, h1686, h1860, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1902 | h1902
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1903 | h1903
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1904 | h1904
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1905 | h1905
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1906 | h1906
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1907 | h1907
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1908 | h1908
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1909 | h1909
                  · rcases h1bigk with h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h0, hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1255, hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1521, hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1521, h1902, h1903, h1908, h1909, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1686, hc01, hc23, hlam, hphi, ht12, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1686, hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1686, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1686, h1903, h1908, h1909, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1685, h1903, h1908, h1909, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1686, hc12, hc23, hlam, hphi, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1521, h1685, h1686, h1903, h1908, h1909, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      rcases p1910_3 (m.d 0 1) (by simp) with h1925 | h1925
                      · linarith only [h1255, h1925, hlam]
                      · linarith only [h1685, h1925, hlam]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1685, h1902, h1903, h1908, h1909, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1902, hlam, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1904, hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1686, h1902, h1903, h1908, h1909, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1685, hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1903, hlam, p1910_1]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1905, hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [h1906, hlam, p1910_0]
                    · have p1910_0 := h1910c.1
                      have p1910_1 := h1910c.2.1
                      have p1910_2 := h1910c.2.2.1
                      have p1910_3 := h1910c.2.2.2
                      linarith only [hlam, p1910_0]
                  · linarith only [h1521, h1685, h1686, h1902, h1906, h1909, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h1521, h1686, h1902, h1908, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h1521, h1686, h1902, h1907, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h1521, h1685, h1903, h1906, hc25, hlam, hphi, u5elo4]
          · linarith only [h1255, h1685, h1903, h1905, hc25, hlam, hphi, u5elo3]
        · linarith only [h1686, h1902, h1904, hlam]
      · linarith only [h1521, h1902, h1903, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1945 | h1945
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1946 | h1946
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1947 | h1947
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1948 | h1948
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1949 | h1949
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1950 | h1950
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1951 | h1951
                  · rcases h1bigk with h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h0, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1255, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1521, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h0, h1945, h1950, h1951, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1686, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1902, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1902, h1945, h1949, h1950, h1951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1685, h1686, h1945, h1950, h1951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h0, h1686, hc02, hc23, hlam, hphi, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1521, h1685, h1686, h1945, h1950, h1951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      rcases p1952_3 (m.d 0 1) (by simp) with h1967 | h1967
                      · linarith only [h1255, h1967, hlam]
                      · linarith only [h1685, h1967, hlam]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1685, h1945, h1950, h1951, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h0, h1685, h1902, h1945, h1949, h1950, h1951, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1946, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      rcases p1952_3 (m.d 0 1) (by simp) with h1974 | h1974
                      · linarith only [h1521, h1974, hlam]
                      · linarith only [h1685, h1974, hlam]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1685, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1945, hlam, p1952_1]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1947, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [h1948, hlam, p1952_0]
                    · have p1952_0 := h1952c.1
                      have p1952_1 := h1952c.2.1
                      have p1952_2 := h1952c.2.2.1
                      have p1952_3 := h1952c.2.2.2
                      linarith only [hlam, p1952_0]
                  · linarith only [h0, h1685, h1902, h1948, h1949, h1951, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1902, h1949, h1950, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h0, h1686, h1949, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h1685, h1902, h1945, h1948, hc25, hlam, hphi, u5elo4]
          · linarith only [h0, h1685, h1902, h1945, h1946, h1947, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1987 | h1987
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1988 | h1988
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1989 | h1989
              · linarith only [h1255, h1685, h1945, h1946, h1989, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h1685, h1686, h1945, h1989, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h0, h1685, h1686, h1945, h1946, h1988, hc25, hlam, hphi, u5elo4]
          · linarith only [h0, h1685, h1686, h1945, h1987, hc25, hlam, hphi, u5elo3]
      · linarith only [h0, h1945, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

end R2N4
