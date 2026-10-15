import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S4
import Jsp000404.R1LeavesN7_54S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h868 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1079 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1211 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1293 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1535 | h1535
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1536 | h1536
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1537 | h1537
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1538 | h1538
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1539 | h1539
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1541 | h1541
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1542 | h1542
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1543 | h1543
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1544 | h1544
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1545 | h1545
                      · linarith only [h1293, h1535, h1540, h1545, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1293, h1537, h1545, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1079, h1535, h1539, h1544, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1293, h1535, h1538, h1539, h1540, h1543, hlam]
                · linarith only [h1293, h1535, h1538, h1539, h1540, h1542, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1293, h1536, h1540, h1541, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1552 | h1552
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1553 | h1553
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1554 | h1554
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1555 | h1555
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1556 | h1556
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1557 | h1557
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1558 | h1558
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1559 | h1559
                            · rcases h0bigk with h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c | h1560c
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h0, hlam, p1560_1]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h868, hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1079, hlam, p1560_1]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1211, hlam, p1560_1]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h0, h1540, hc01, hc23, hlam, hphi, ht12, p1560_1]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1293, hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h0, h1536, h1539, h1540, h1557, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1560_1, u3ehi4]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h0, h1536, h1540, h1557, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1560_1, u3ehi4]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                rcases p1560_3 (m.d 0 1) (by simp) with h1571 | h1571
                                · linarith only [h1571, h868, hlam]
                                · rcases p1560_3 (m.d 0 2) (by simp) with h1573 | h1573
                                  · linarith only [h1293, h1573, hlam]
                                  · linarith only [h0, h1573, hlam]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1535, h1557, h1558, hlam, hphi, ht0b, ht34, ht45, ht5b, p1560_1, u0elo2, u3ehi4]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1535, h1557, h1558, hlam, hphi, ht0b, ht34, ht45, ht5b, p1560_1, u0elo2, u3ehi4]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1536, h1557, hlam, hphi, ht0b, ht34, ht45, ht5b, p1560_1, u0elo2, u3ehi4]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h0, h1535, h1540, hc01, hc23, hlam, hphi, ht12, p1560_1]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1535, hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1537, hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h0, h1535, h1536, h1540, h1557, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1560_1, u3ehi4]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h0, h1536, h1540, hc01, hc23, hlam, hphi, ht12, p1560_1]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1536, hlam, p1560_1]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1538, hlam, p1560_0]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [h1539, hlam, p1560_1]
                              · have p1560_0 := h1560c.1
                                have p1560_1 := h1560c.2.1
                                have p1560_2 := h1560c.2.2.1
                                have p1560_3 := h1560c.2.2.2
                                linarith only [hlam, p1560_0]
                            · linarith only [h0, h1535, h1539, h1540, h1559, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1535, h1539, h1540, h1556, h1558, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1540, h1557, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h1535, h1537, h1540, h1556, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h1079, h1539, h1555, hlam]
                  · linarith only [h1538, h1554, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · linarith only [h1537, h1553, h868, hlam]
              · linarith only [h0, h1536, h1552, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1598 | h1598
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1599 | h1599
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1600 | h1600
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1601 | h1601
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1602 | h1602
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1603 | h1603
                      · linarith only [h1293, h1535, h1598, h1603, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1293, h1537, h1603, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1606 | h1606
                      · linarith only [h1293, h1535, h1598, h1606, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1293, h1537, h1606, hlam]
                  · linarith only [h1537, h1601, h868, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1293, h1537, h1598, h1600, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1293, h1536, h1537, h1539, h1598, h1599, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1612 | h1612
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1613 | h1613
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1614 | h1614
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1615 | h1615
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1616 | h1616
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1617 | h1617
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1618 | h1618
                          · linarith only [h1535, h1539, h1618, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1620 | h1620
                            · linarith only [h1535, h1539, h1616, h1620, hlam]
                            · rcases h0bigk with h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h0, hlam, p1622_1]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h868, hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1079, hlam, p1622_1]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1211, hlam, p1622_1]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1293, hc01, hc23, hlam, hphi, ht12, p1622_1]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1293, hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1293, h1535, h1616, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1622_1, u3ehi3]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1293, h1535, h1539, h1616, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1622_1, u3ehi3]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                rcases p1622_3 (m.d 0 1) (by simp) with h1633 | h1633
                                · linarith only [h1633, h868, hlam]
                                · rcases p1622_3 (m.d 0 2) (by simp) with h1635 | h1635
                                  · linarith only [h1293, h1635, hlam]
                                  · linarith only [h0, h1635, hlam]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1535, h1616, hlam, hphi, ht0b, ht34, ht45, ht5b, p1622_1, u0elo2, u3ehi3]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1535, h1616, hlam, hphi, ht0b, ht34, ht45, ht5b, p1622_1, u0elo2, u3ehi3]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1535, h1539, h1616, hlam, hphi, ht0b, ht34, ht45, ht5b, p1622_1, u0elo2, u3ehi3]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1539, h1613, h1615, hc01, hc13, hlam, hphi, p1622_1]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1535, hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1537, hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1539, hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h0, h1536, h1598, hc01, hc23, hlam, hphi, ht12, p1622_1]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1536, hlam, p1622_1]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h1538, hlam, p1622_0]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [h0, h1079, h1536, h1598, hc01, hc23, hlam, hphi, ht12, p1622_1]
                              · have p1622_0 := h1622c.1
                                have p1622_1 := h1622c.2.1
                                have p1622_2 := h1622c.2.2.1
                                have p1622_3 := h1622c.2.2.2
                                linarith only [hlam, p1622_0]
                        · linarith only [h1535, h1539, h1598, h1613, h1615, h1616, h1617, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1598, h1616, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1654 | h1654
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1655 | h1655
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1656 | h1656
                          · linarith only [h1535, h1539, h1656, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1658 | h1658
                            · linarith only [h1079, h1536, h1615, h1654, h1656, h1658, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases h0bigk with h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h0, hlam, p1660_1]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h868, hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1079, hlam, p1660_1]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1211, hlam, p1660_1]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h0, h1598, hc01, hc23, hlam, hphi, ht12, p1660_1]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1293, hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h0, h1535, h1598, h1654, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1660_1, u3ehi3]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h0, h1211, h1598, hc01, hc23, hlam, hphi, ht12, p1660_1]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                rcases p1660_3 (m.d 0 1) (by simp) with h1671 | h1671
                                · linarith only [h1671, h868, hlam]
                                · rcases p1660_3 (m.d 0 2) (by simp) with h1673 | h1673
                                  · linarith only [h1293, h1673, hlam]
                                  · linarith only [h0, h1673, hlam]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1536, hc25, hlam, hphi, ht0b, ht5b, p1660_1, u0elo2]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1535, h1654, hlam, hphi, ht0b, ht34, ht45, ht5b, p1660_1, u0elo2, u3ehi3]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1536, h1655, hlam, hphi, ht0b, ht34, ht45, ht5b, p1660_1, u0elo2, u3ehi4]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h0, h1079, h1536, h1598, h1615, h1655, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p1660_1, u3ehi4]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1535, hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1537, hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1539, hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h0, h1536, h1598, hc01, hc23, hlam, hphi, ht12, p1660_1]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1536, hlam, p1660_1]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h1538, hlam, p1660_0]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [h0, h1079, h1536, h1598, hc01, hc23, hlam, hphi, ht12, p1660_1]
                              · have p1660_0 := h1660c.1
                                have p1660_1 := h1660c.2.1
                                have p1660_2 := h1660c.2.2.1
                                have p1660_3 := h1660c.2.2.2
                                linarith only [hlam, p1660_0]
                        · linarith only [h0, h1598, h1655, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h1536, h1537, h1539, h1598, h1654, hlam]
                  · linarith only [h0, h1536, h1538, h1598, h1614, h868, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h1537, h1538, h1613, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
              · linarith only [h0, h1536, h1612, hlam]
        · linarith only [h1537, h1538, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1293, h1535, h1537, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1697 | h1697
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1698 | h1698
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1699 | h1699
          · linarith only [h1535, h1536, h1699, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1701 | h1701
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1702 | h1702
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1703 | h1703
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1704 | h1704
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1705 | h1705
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1706 | h1706
                      · linarith only [h1293, h1535, h1701, h1706, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1293, h1698, h1706, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1709 | h1709
                      · linarith only [h1535, h1536, h1702, h1709, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1293, h1697, h1709, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1697, h1704, h868, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1293, h1535, h1697, h1701, h1703, hlam]
              · linarith only [h1293, h1535, h1697, h1701, h1702, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1715 | h1715
              · linarith only [h1535, h1536, h1697, h1701, h1715, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1717 | h1717
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1718 | h1718
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1719 | h1719
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1720 | h1720
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1721 | h1721
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1722 | h1722
                          · linarith only [h1535, h1536, h1699, h1722, hlam]
                          · linarith only [h0, h1715, h1717, h1719, h1722, hc01, hc13, hlam, hphi]
                        · linarith only [h1535, h1536, h1698, h1699, h1701, h1717, h1719, h1720, h1721, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                      · linarith only [h1698, h1701, h1720, h868, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1727 | h1727
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1728 | h1728
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1729 | h1729
                          · linarith only [h1079, h1535, h1719, h1729, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h1535, h1715, h1727, h1729, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h1698, h1701, h1728, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h1701, h1727, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1698, h1718, h868, hlam]
                · linarith only [h1697, h1698, h1717, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
        · linarith only [h1697, h1698, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1293, h1535, h1697, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1738 | h1738
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1739 | h1739
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1740 | h1740
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1741 | h1741
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1742 | h1742
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1743 | h1743
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1744 | h1744
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1745 | h1745
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1746 | h1746
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1747 | h1747
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1748 | h1748
                        · linarith only [h1535, h1738, h1742, h1747, h1748, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h1293, h1739, h1748, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1293, h1738, h1739, h1740, h1747, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                    · linarith only [h1079, h1293, h1738, h1740, h1741, h1742, h1746, hc01, hc12, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                  · linarith only [h1293, h1738, h1740, h1742, h1745, hlam]
                · linarith only [h1293, h1739, h1742, h1744, hlam]
              · linarith only [h1293, h1738, h1740, h1742, h1743, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1756 | h1756
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1757 | h1757
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1758 | h1758
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1759 | h1759
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1760 | h1760
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1761 | h1761
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1762 | h1762
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1763 | h1763
                            · rcases h0bigk with h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c | h1764c
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [hlam, p1764_0]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h0, hlam, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h868, hlam, p1764_0]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1079, hlam, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1211, hlam, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h0, h1742, hc01, hc23, hlam, hphi, ht12, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [hlam, p1764_0]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1293, hlam, p1764_0]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1535, hlam, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h0, h1211, h1742, hc01, hc23, hlam, hphi, ht12, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                rcases p1764_3 (m.d 0 1) (by simp) with h1775 | h1775
                                · linarith only [h1775, h868, hlam]
                                · rcases p1764_3 (m.d 0 2) (by simp) with h1777 | h1777
                                  · linarith only [h1293, h1777, hlam]
                                  · linarith only [h0, h1777, hlam]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1738, h1761, hlam, hphi, ht0b, ht34, ht45, ht5b, p1764_1, u0elo2, u3ehi4]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [hlam, p1764_0]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1535, h1738, h1761, hlam, hphi, ht0b, ht34, ht45, ht5b, p1764_1, u0elo2, u3ehi4]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1738, h1761, hlam, hphi, ht0b, ht34, ht45, ht5b, p1764_1, u0elo2, u3ehi4]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                rcases p1764_3 (m.d 0 1) (by simp) with h1784 | h1784
                                · linarith only [h1079, h1784, hlam]
                                · rcases p1764_3 (m.d 0 2) (by simp) with h1786 | h1786
                                  · linarith only [h1535, h1786, hlam]
                                  · linarith only [h0, h1786, hlam]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1738, h1761, hlam, hphi, ht0b, ht34, ht45, ht5b, p1764_1, u0elo3, u3ehi4]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1739, hlam, p1764_0]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [hlam, p1764_0]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1738, h1739, h1761, hlam, hphi, ht0b, ht34, ht45, ht5b, p1764_1, u0elo2, u3ehi4]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1211, h1742, h1756, hc01, hc23, hlam, hphi, ht12, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1738, hlam, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1740, hlam, p1764_0]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [h1741, hlam, p1764_1]
                              · have p1764_0 := h1764c.1
                                have p1764_1 := h1764c.2.1
                                have p1764_2 := h1764c.2.2.1
                                have p1764_3 := h1764c.2.2.2
                                linarith only [hlam, p1764_0]
                            · linarith only [h1739, h1741, h1763, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                          · linarith only [h1535, h1738, h1739, h1741, h1761, h1762, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                        · linarith only [h0, h1742, h1761, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1293, h1738, h1740, h1760, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1079, h1741, h1759, hlam]
                  · linarith only [h1738, h1739, h1740, h1758, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h1740, h1757, h868, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1738, h1756, hlam]
          · linarith only [h1535, h1738, h1741, hlam]
        · linarith only [h1739, h1740, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1808 | h1808
        · linarith only [h1739, h1808, hc34, hlam, hphi, u3ehi4]
        · linarith only [h1293, h1738, h1808, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1811 | h1811
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1812 | h1812
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1813 | h1813
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1814 | h1814
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1815 | h1815
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1816 | h1816
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1817 | h1817
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1818 | h1818
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1819 | h1819
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1820 | h1820
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1821 | h1821
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1822 | h1822
                            · rcases h0bigk with h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h0, hlam, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h868, hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1079, hlam, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1211, hlam, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1738, h1814, h1819, h1821, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1293, hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1535, hlam, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1738, hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1293, h1814, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h0, h1293, h1814, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h0, h1293, h1738, h1813, h1814, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h0, h1293, h1738, h1814, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1535, h1814, h1819, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h0, h1535, h1814, h1819, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1811, hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1535, h1812, h1814, h1819, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1823_1, u3ehi4]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1738, h1814, h1819, h1821, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h0, h1738, h1814, h1819, h1821, hc01, hc12, hlam, hphi, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1812, hlam, p1823_0]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [h1813, hlam, p1823_1]
                              · have p1823_0 := h1823c.1
                                have p1823_1 := h1823c.2.1
                                have p1823_2 := h1823c.2.2.1
                                have p1823_3 := h1823c.2.2.2
                                linarith only [hlam, p1823_0]
                            · linarith only [h1535, h1813, h1814, h1819, h1822, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1535, h1813, h1821, hlam]
                        · linarith only [h1293, h1811, h1820, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1293, h1811, h1819, hlam]
                    · linarith only [h1079, h1813, h1818, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1293, h1812, h1814, h1817, hlam]
                · linarith only [h1293, h1812, h1814, h1816, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1293, h1812, h1814, h1815, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1857 | h1857
              · linarith only [h0, h1738, h1814, h1857, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1859 | h1859
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1860 | h1860
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1861 | h1861
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1862 | h1862
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1863 | h1863
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1864 | h1864
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1865 | h1865
                            · rcases h0bigk with h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h0, hlam, p1866_1]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h868, hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1079, hlam, p1866_1]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1211, hlam, p1866_1]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h0, h1857, h1864, hc01, hc24, hlam, hphi, ht12, p1866_1]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1293, hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1535, hlam, p1866_1]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1738, hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                rcases p1866_3 (m.d 0 1) (by simp) with h1877 | h1877
                                · linarith only [h1877, h868, hlam]
                                · rcases p1866_3 (m.d 0 2) (by simp) with h1879 | h1879
                                  · linarith only [h1293, h1879, hlam]
                                  · linarith only [h0, h1879, hlam]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                rcases p1866_3 (m.d 0 1) (by simp) with h1882 | h1882
                                · linarith only [h1882, h868, hlam]
                                · rcases p1866_3 (m.d 0 2) (by simp) with h1884 | h1884
                                  · linarith only [h1293, h1884, hlam]
                                  · rcases p1866_3 (m.d 0 3) (by simp) with h1886 | h1886
                                    · rcases p1866_3 (m.d 0 4) (by simp) with h1887 | h1887
                                      · linarith only [h1811, h1887, hlam]
                                      · linarith only [h1535, h1887, hlam]
                                    · linarith only [h1293, h1886, hlam]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1811, h1865, hc45, hlam, hphi, ht0b, ht5b, p1866_1, u0elo2]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1812, hlam, hphi, ht0b, ht34, ht45, ht5b, p1866_1, u0elo2, u3ehi4]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                rcases p1866_3 (m.d 0 1) (by simp) with h1894 | h1894
                                · linarith only [h1079, h1894, hlam]
                                · rcases p1866_3 (m.d 0 2) (by simp) with h1896 | h1896
                                  · linarith only [h1535, h1896, hlam]
                                  · linarith only [h0, h1896, hlam]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                rcases p1866_3 (m.d 0 1) (by simp) with h1899 | h1899
                                · linarith only [h1079, h1899, hlam]
                                · rcases p1866_3 (m.d 0 2) (by simp) with h1901 | h1901
                                  · linarith only [h1535, h1901, hlam]
                                  · rcases p1866_3 (m.d 0 3) (by simp) with h1903 | h1903
                                    · rcases p1866_3 (m.d 0 4) (by simp) with h1904 | h1904
                                      · rcases p1866_3 (m.d 0 5) (by simp) with h1905 | h1905
                                        · linarith only [h1813, h1905, hlam]
                                        · linarith only [h1738, h1905, hlam]
                                      · linarith only [h1535, h1904, hlam]
                                    · linarith only [h1293, h1903, hlam]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1811, hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1811, h1812, hlam, hphi, ht0b, ht34, ht45, ht5b, p1866_1, u0elo2, u3ehi4]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                rcases p1866_3 (m.d 0 1) (by simp) with h1913 | h1913
                                · linarith only [h1211, h1913, hlam]
                                · rcases p1866_3 (m.d 0 2) (by simp) with h1915 | h1915
                                  · linarith only [h1738, h1915, hlam]
                                  · linarith only [h0, h1915, hlam]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                rcases p1866_3 (m.d 0 1) (by simp) with h1918 | h1918
                                · linarith only [h1211, h1918, hlam]
                                · rcases p1866_3 (m.d 0 2) (by simp) with h1920 | h1920
                                  · linarith only [h1738, h1920, hlam]
                                  · rcases p1866_3 (m.d 0 3) (by simp) with h1922 | h1922
                                    · rcases p1866_3 (m.d 0 4) (by simp) with h1923 | h1923
                                      · rcases p1866_3 (m.d 0 5) (by simp) with h1924 | h1924
                                        · rcases h2bigk with h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c | h1925c
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h0, hlam, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1293, hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1535, hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1738, hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h0, h1814, hc01, hc23, hlam, hphi, ht12, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1814, hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1857, h1864, hlam, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1857, hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            rcases p1925_3 (m.d 0 2) (by simp) with h1936 | h1936
                                            · linarith only [h1936, hlam, p1925_0]
                                            · rcases p1925_3 (m.d 1 2) (by simp) with h1938 | h1938
                                              · linarith only [h1814, h1938, hlam]
                                              · linarith only [h0, h1938, hlam]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h0, h1535, hc01, hc23, hlam, hphi, ht12, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h0, h1211, h1857, hc01, hc23, hlam, hphi, ht12, p1866_1, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            rcases p1925_3 (m.d 0 2) (by simp) with h1945 | h1945
                                            · linarith only [h1945, hlam, p1925_0]
                                            · rcases p1925_3 (m.d 1 2) (by simp) with h1947 | h1947
                                              · linarith only [h0, h1211, h1814, h1857, h1864, h1947, hc01, hc23, hlam, hphi, ht12, p1866_1]
                                              · linarith only [h0, h1947, hlam]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1862, hlam, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h0, h1211, h1857, h1862, hc01, hc23, hlam, hphi, ht12, p1866_1, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            rcases p1925_3 (m.d 0 2) (by simp) with h1954 | h1954
                                            · linarith only [h1954, hlam, p1925_0]
                                            · rcases p1925_3 (m.d 1 2) (by simp) with h1956 | h1956
                                              · linarith only [h1857, h1956, hlam]
                                              · linarith only [h0, h1956, hlam]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1863, hlam, p1925_1]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [h1864, hlam, p1925_0]
                                          · have p1925_0 := h1925c.1
                                            have p1925_1 := h1925c.2.1
                                            have p1925_2 := h1925c.2.2.1
                                            have p1925_3 := h1925c.2.2.2
                                            linarith only [hlam, p1925_0]
                                        · linarith only [h1738, h1924, hlam]
                                      · linarith only [h1535, h1923, hlam]
                                    · linarith only [h1293, h1922, hlam]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1812, hlam, p1866_0]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [h1813, hlam, p1866_1]
                              · have p1866_0 := h1866c.1
                                have p1866_1 := h1866c.2.1
                                have p1866_2 := h1866c.2.2.1
                                have p1866_3 := h1866c.2.2.2
                                linarith only [hlam, p1866_0]
                            · linarith only [h1811, h1813, h1865, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                          · linarith only [h0, h1535, h1811, h1813, h1864, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1293, h1811, h1863, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1811, h1814, h1862, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1079, h1813, h1861, hlam]
                  · linarith only [h1812, h1860, h868, hlam]
                · linarith only [h1811, h1859, h868, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1976 | h1976
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1977 | h1977
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1978 | h1978
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1979 | h1979
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1980 | h1980
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1981 | h1981
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1982 | h1982
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1983 | h1983
                          · linarith only [h1811, h1813, h1976, h1981, h1983, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1535, h1980, h1983, hc01, hc14, hlam, hphi]
                        · linarith only [h1293, h1812, h1982, hlam]
                      · linarith only [h1293, h1811, h1812, h1981, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1988 | h1988
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1989 | h1989
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1990 | h1990
                          · linarith only [h1079, h1980, h1990, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1992 | h1992
                            · linarith only [h0, h1535, h1811, h1990, h1992, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · rcases h0bigk with h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h0, hlam, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h868, hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1079, hlam, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1211, hlam, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1293, h1976, hc01, hc12, hlam, hphi, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1293, hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1535, hlam, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1738, hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1293, h1976, hc01, hc12, hlam, hphi, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h0, h1293, h1976, hc01, hc12, hlam, hphi, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1079, h1293, h1976, hc01, hc12, hlam, hphi, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1211, h1293, h1976, hc01, hc12, hlam, hphi, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1293, h1535, h1812, h1976, h1990, h1992, hc01, hc12, hc45, hlam, hphi, ht34, p1994_1, u3ehi3]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h0, h1293, h1535, h1812, h1976, h1990, h1992, hc01, hc12, hc45, hlam, hphi, ht34, p1994_1, u3ehi3]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1811, hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1813, hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1293, h1812, h1976, hc01, hc12, hlam, hphi, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h0, h1293, h1812, h1976, hc01, hc12, hlam, hphi, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1812, hlam, p1994_0]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [h1079, h1293, h1812, h1976, hc01, hc12, hlam, hphi, p1994_1]
                              · have p1994_0 := h1994c.1
                                have p1994_1 := h1994c.2.1
                                have p1994_2 := h1994c.2.2.1
                                have p1994_3 := h1994c.2.2.2
                                linarith only [hlam, p1994_0]
                        · linarith only [h1293, h1812, h1989, hlam]
                      · linarith only [h1293, h1811, h1812, h1988, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                  · linarith only [h1293, h1812, h1976, h1979, hlam]
                · linarith only [h1293, h1811, h1976, h1978, hlam]
              · linarith only [h1293, h1811, h1976, h1977, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2025 | h2025
              · linarith only [h0, h1738, h1976, h2025, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2027 | h2027
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2028 | h2028
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2029 | h2029
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2030 | h2030
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2031 | h2031
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2032 | h2032
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2033 | h2033
                            · linarith only [h1811, h1813, h2033, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h0, hlam, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h868, hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1079, hlam, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1211, hlam, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h0, h2025, h2030, h2032, hc01, hc23, hlam, hphi, ht12, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1293, hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1535, hlam, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1738, hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                rcases p2035_3 (m.d 0 1) (by simp) with h2046 | h2046
                                · linarith only [h2046, h868, hlam]
                                · rcases p2035_3 (m.d 0 2) (by simp) with h2048 | h2048
                                  · linarith only [h1293, h2048, hlam]
                                  · linarith only [h0, h2048, hlam]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                rcases p2035_3 (m.d 0 1) (by simp) with h2051 | h2051
                                · linarith only [h2051, h868, hlam]
                                · rcases p2035_3 (m.d 0 2) (by simp) with h2053 | h2053
                                  · linarith only [h1293, h2053, hlam]
                                  · rcases p2035_3 (m.d 0 3) (by simp) with h2055 | h2055
                                    · rcases p2035_3 (m.d 0 4) (by simp) with h2056 | h2056
                                      · linarith only [h1811, h2056, hlam]
                                      · linarith only [h1535, h2056, hlam]
                                    · linarith only [h1293, h2055, hlam]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1811, hlam, hphi, ht0b, ht34, ht45, ht5b, p2035_1, u0elo2, u3ehi3]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1812, hlam, hphi, ht0b, ht34, ht45, ht5b, p2035_1, u0elo2, u3ehi4]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1813, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h0, h1813, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1811, hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1813, hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1813, h1976, h2027, h2029, hc01, hc23, hlam, hphi, ht12, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h0, h1813, h1976, h2027, h2029, hc01, hc23, hlam, hphi, ht12, p2035_1]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1812, hlam, p2035_0]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [h1811, h1813, h1976, h2027, h2029, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2035_1, u3ehi3]
                              · have p2035_0 := h2035c.1
                                have p2035_1 := h2035c.2.1
                                have p2035_2 := h2035c.2.2.1
                                have p2035_3 := h2035c.2.2.2
                                linarith only [hlam, p2035_0]
                          · linarith only [h0, h1535, h1976, h2027, h2029, h2032, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h1811, h1976, h2031, h868, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1811, h1813, h1976, h2027, h2029, h2030, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2076 | h2076
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2077 | h2077
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2078 | h2078
                          · linarith only [h1079, h2029, h2078, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2080 | h2080
                            · linarith only [h0, h1738, h1811, h2078, h2080, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h0, hlam, p2082_1]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h868, hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1079, hlam, p2082_1]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1211, hlam, p2082_1]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h0, h2025, hc01, hc25, hlam, hphi, ht12, p2082_1]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1293, hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1535, hlam, p2082_1]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1738, hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                rcases p2082_3 (m.d 0 1) (by simp) with h2093 | h2093
                                · linarith only [h2093, h868, hlam]
                                · rcases p2082_3 (m.d 0 2) (by simp) with h2095 | h2095
                                  · linarith only [h1293, h2095, hlam]
                                  · linarith only [h0, h2095, hlam]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                rcases p2082_3 (m.d 0 1) (by simp) with h2098 | h2098
                                · linarith only [h2098, h868, hlam]
                                · rcases p2082_3 (m.d 0 2) (by simp) with h2100 | h2100
                                  · linarith only [h1293, h2100, hlam]
                                  · rcases p2082_3 (m.d 0 3) (by simp) with h2102 | h2102
                                    · rcases p2082_3 (m.d 0 4) (by simp) with h2103 | h2103
                                      · linarith only [h1811, h2103, hlam]
                                      · linarith only [h1535, h2103, hlam]
                                    · linarith only [h1293, h2102, hlam]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1811, hlam, hphi, ht0b, ht34, ht45, ht5b, p2082_1, u0elo2, u3ehi3]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1811, h1813, hlam, hphi, ht0b, ht34, ht45, ht5b, p2082_1, u0elo2, u3ehi3]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1535, h2078, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2082_1]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1535, h2078, hc02, hc45, hlam, hphi, ht23, ht34, p2082_1]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1811, hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1813, hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                rcases p2082_3 (m.d 0 1) (by simp) with h2115 | h2115
                                · linarith only [h1211, h2115, hlam]
                                · rcases p2082_3 (m.d 0 2) (by simp) with h2117 | h2117
                                  · linarith only [h1738, h2117, hlam]
                                  · linarith only [h0, h2117, hlam]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                rcases p2082_3 (m.d 0 1) (by simp) with h2120 | h2120
                                · linarith only [h1211, h2120, hlam]
                                · rcases p2082_3 (m.d 0 2) (by simp) with h2122 | h2122
                                  · linarith only [h1738, h2122, hlam]
                                  · rcases p2082_3 (m.d 0 3) (by simp) with h2124 | h2124
                                    · rcases p2082_3 (m.d 0 4) (by simp) with h2125 | h2125
                                      · linarith only [h1813, h2125, hlam]
                                      · linarith only [h1535, h2125, hlam]
                                    · linarith only [h1293, h2124, hlam]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1812, hlam, p2082_0]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [h1811, hlam, hphi, ht0b, ht34, ht45, ht5b, p2082_1, u0elo4, u3ehi3]
                              · have p2082_0 := h2082c.1
                                have p2082_1 := h2082c.2.1
                                have p2082_2 := h2082c.2.2.1
                                have p2082_3 := h2082c.2.2.2
                                linarith only [hlam, p2082_0]
                        · linarith only [h1812, h2077, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · linarith only [h1811, h1812, h1976, h2076, h868, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                  · linarith only [h1811, h2028, h868, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1811, h2027, h868, hlam]
        · linarith only [h1811, h1812, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2137 | h2137
        · linarith only [h1811, h2137, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2139 | h2139
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2140 | h2140
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2141 | h2141
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2142 | h2142
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2143 | h2143
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2144 | h2144
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2145 | h2145
                      · linarith only [h1811, h2140, h2145, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h1293, h2140, h2142, h2145, hc01, hc12, hlam, hphi]
                    · linarith only [h1079, h1811, h2139, h2140, h2142, h2144, hc01, hc12, hlam, hphi]
                  · linarith only [h2142, h2143, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2150 | h2150
                  · linarith only [h2142, h2150, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2152 | h2152
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2153 | h2153
                      · linarith only [h2142, h2153, h868, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2155 | h2155
                        · linarith only [h2140, h2142, h2155, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2157 | h2157
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2158 | h2158
                            · rcases h0bigk with h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [hlam, p2159_0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h0, hlam, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h868, hlam, p2159_0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1079, hlam, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1211, hlam, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1293, h2140, h2150, h2158, hc01, hc34, hlam, hphi, ht12, ht23, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [hlam, p2159_0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1293, hlam, p2159_0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1535, hlam, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1738, hlam, p2159_0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h2150, h2158, h868, hc01, hc34, hlam, hphi, ht12, ht23, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1293, h2140, h2150, h2158, hc02, hc34, hlam, hphi, ht23, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [hlam, p2159_0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1811, hlam, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h2137, hlam, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                rcases p2159_3 (m.d 0 1) (by simp) with h2175 | h2175
                                · linarith only [h1079, h2175, hlam]
                                · rcases p2159_3 (m.d 0 2) (by simp) with h2177 | h2177
                                  · linarith only [h1535, h2177, hlam]
                                  · linarith only [h0, h2177, hlam]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                rcases p2159_3 (m.d 0 1) (by simp) with h2180 | h2180
                                · linarith only [h1079, h2180, hlam]
                                · rcases p2159_3 (m.d 0 2) (by simp) with h2182 | h2182
                                  · linarith only [h1535, h2182, hlam]
                                  · rcases p2159_3 (m.d 0 3) (by simp) with h2184 | h2184
                                    · linarith only [h1811, h2184, hlam]
                                    · linarith only [h1293, h2184, hlam]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p2159_1, u0elo3, u3ehi0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [hlam, p2159_0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h2137, hlam, hphi, ht0b, ht34, ht45, ht5b, p2159_1, u0elo3, u3ehi0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h1738, h2141, hc01, hc12, hlam, hphi, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h0, h1738, h2141, hc01, hc12, hlam, hphi, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p2159_1, u0elo4, u3ehi0]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [h2139, hlam, p2159_1]
                              · have p2159_0 := h2159c.1
                                have p2159_1 := h2159c.2.1
                                have p2159_2 := h2159c.2.2.1
                                have p2159_3 := h2159c.2.2.2
                                linarith only [hlam, p2159_0]
                            · linarith only [h2139, h2158, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h1535, h2139, h2157, hlam]
                    · linarith only [h1079, h2139, h2152, hlam]
              · linarith only [h0, h1293, h2140, h2141, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2199 | h2199
              · linarith only [h0, h1738, h2140, h2199, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2201 | h2201
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2202 | h2202
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2203 | h2203
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2204 | h2204
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2205 | h2205
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2206 | h2206
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2207 | h2207
                            · rcases h0bigk with h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [hlam, p2208_0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h0, hlam, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h868, hlam, p2208_0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1079, hlam, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1211, hlam, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h0, h2199, h2204, h2206, hc01, hc23, hlam, hphi, ht12, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [hlam, p2208_0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1293, hlam, p2208_0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1535, hlam, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1738, hlam, p2208_0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1811, h2140, h2201, hc01, hc23, hlam, hphi, ht12, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h0, h1811, h2140, h2201, hc01, hc23, hlam, hphi, ht12, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [hlam, p2208_0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1811, hlam, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h2137, hlam, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1811, h2140, h2201, hc01, hc23, hlam, hphi, ht12, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h0, h1811, h2140, h2201, hc01, hc23, hlam, hphi, ht12, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1811, h2140, h2201, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2208_1, u3ehi0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [hlam, p2208_0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1211, h1811, h2140, h2201, hc01, hc23, hlam, hphi, ht12, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h1811, h2139, h2140, h2201, hc01, hc23, hlam, hphi, ht12, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h0, h1811, h2139, h2140, h2201, hc01, hc23, hlam, hphi, ht12, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p2208_1, u0elo4, u3ehi0]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [h2139, hlam, p2208_1]
                              · have p2208_0 := h2208c.1
                                have p2208_1 := h2208c.2.1
                                have p2208_2 := h2208c.2.2.1
                                have p2208_3 := h2208c.2.2.2
                                linarith only [hlam, p2208_0]
                            · linarith only [h1811, h2139, h2207, hlam]
                          · linarith only [h0, h1535, h1811, h2139, h2140, h2201, h2206, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h2140, h2201, h2205, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h2140, h2201, h2204, hlam]
                    · linarith only [h1079, h1811, h2139, h2140, h2201, h2203, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, u0elo3, u3ehi0]
                  · linarith only [h1811, h2201, h2202, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2240 | h2240
                  · linarith only [h2201, h2240, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2242 | h2242
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2243 | h2243
                      · linarith only [h0, h2140, h2201, h2243, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h2140, h2243, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1079, h2139, h2242, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2247 | h2247
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2248 | h2248
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2249 | h2249
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2250 | h2250
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2251 | h2251
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2252 | h2252
                      · linarith only [h1811, h2247, h2252, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h1293, h2247, h2249, h2252, hc01, hc12, hlam, hphi]
                    · linarith only [h1811, h2249, h2251, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h1811, h2249, h2250, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2257 | h2257
                  · linarith only [h2249, h2257, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2259 | h2259
                    · linarith only [h1811, h2139, h2249, h2259, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2261 | h2261
                      · linarith only [h2247, h2249, h2259, h2261, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2263 | h2263
                        · linarith only [h2247, h2257, h2263, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2265 | h2265
                          · linarith only [h0, h1293, h2247, h2249, h2259, h2265, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2267 | h2267
                            · linarith only [h0, h1293, h2247, h2249, h2259, h2267, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1811, h2267, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h0, h1293, h2247, h2248, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2271 | h2271
              · linarith only [h0, h1738, h2247, h2271, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2273 | h2273
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2274 | h2274
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2275 | h2275
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2276 | h2276
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2277 | h2277
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2278 | h2278
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2279 | h2279
                            · linarith only [h1811, h2139, h2279, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h1811, h2247, h2273, h2275, h2279, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h0, h1535, h2247, h2273, h2275, h2278, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h2247, h2274, h2277, hlam]
                      · linarith only [h2247, h2274, h2276, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1811, h2273, h2275, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h1811, h2273, h2274, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2287 | h2287
                  · linarith only [h2273, h2287, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2289 | h2289
                    · linarith only [h1811, h2139, h2273, h2289, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2291 | h2291
                      · linarith only [h2273, h2291, h868, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h2247, h2291, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h868 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1079 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1211 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1293 | h1293
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h868 h1079 h1211 h1293
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h868 h1079 h1211 h1293

set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h868 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1079 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1211 | h1211
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h868 h1079 h1211
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h868 h1079 h1211

set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h868 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1079 | h1079
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h868 h1079
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h868 h1079

set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h868 | h868
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h868
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h868

set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
