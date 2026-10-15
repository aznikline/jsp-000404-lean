import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1025 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1371 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1499 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1500 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h1501 | h1501
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1502 | h1502
    · linarith only [h0, h1502, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1504 | h1504
      · linarith only [h0, h1025, h1504, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1506 | h1506
        · linarith only [h0, h1371, h1506, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1508 | h1508
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1509 | h1509
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1510 | h1510
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1511 | h1511
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1512 | h1512
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1513 | h1513
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1514 | h1514
                      · linarith only [h1, h1508, h1514, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h1510, h1514, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h1025, h1510, h1513, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h1, h1509, h1512, h4, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h1499, h1511, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1520 | h1520
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1521 | h1521
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1522 | h1522
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1523 | h1523
                      · linarith only [h1508, h1510, h1523, hlam]
                      · rcases h0bigk with h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          rcases p1525_3 (m.d 0 1) (by simp) with h1527 | h1527
                          · rcases p1525_3 (m.d 0 2) (by simp) with h1528 | h1528
                            · linarith only [h0, h1528, hlam]
                            · rcases p1525_3 (m.d 0 3) (by simp) with h1530 | h1530
                              · linarith only [h1, h1530, hlam]
                              · linarith only [h1530, h4, hlam]
                          · linarith only [h0, h1527, hlam]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1499, h1501, h1504, h1510, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u0elo0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1501, h1504, h1510, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u0elo0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1501, h1504, h1510, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u0elo0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h0, hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h4, hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1025, hlam, p1525_1]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1371, hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1, hlam, p1525_1]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          rcases p1525_3 (m.d 0 1) (by simp) with h1543 | h1543
                          · rcases p1525_3 (m.d 0 2) (by simp) with h1544 | h1544
                            · linarith only [h1544, h4, hlam]
                            · rcases p1525_3 (m.d 0 3) (by simp) with h1546 | h1546
                              · rcases p1525_3 (m.d 0 4) (by simp) with h1547 | h1547
                                · linarith only [h1499, h1547, hlam]
                                · linarith only [h1025, h1547, hlam]
                              · linarith only [h1546, h4, hlam]
                          · linarith only [h0, h1543, hlam]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1501, h1504, h1510, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u0elo2]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1, h1501, h1504, h1510, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u0elo0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h2, hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          rcases p1525_3 (m.d 0 1) (by simp) with h1556 | h1556
                          · rcases p1525_3 (m.d 0 2) (by simp) with h1557 | h1557
                            · linarith only [h1025, h1557, hlam]
                            · rcases p1525_3 (m.d 0 3) (by simp) with h1559 | h1559
                              · rcases p1525_3 (m.d 0 4) (by simp) with h1560 | h1560
                                · rcases p1525_3 (m.d 0 5) (by simp) with h1561 | h1561
                                  · linarith only [h1501, h1561, hlam]
                                  · linarith only [h1371, h1561, hlam]
                                · linarith only [h1025, h1560, hlam]
                              · linarith only [h1559, h4, hlam]
                          · linarith only [h0, h1556, hlam]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1499, hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1501, h1504, h1510, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1525_1, u0elo3]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h3, hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          rcases p1525_3 (m.d 0 1) (by simp) with h1571 | h1571
                          · rcases p1525_3 (m.d 0 2) (by simp) with h1572 | h1572
                            · linarith only [h1371, h1572, hlam]
                            · rcases p1525_3 (m.d 0 3) (by simp) with h1574 | h1574
                              · rcases p1525_3 (m.d 0 4) (by simp) with h1575 | h1575
                                · rcases p1525_3 (m.d 0 5) (by simp) with h1576 | h1576
                                  · rcases h2bigk with h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1525_1, p1577_1, u0elo4]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h4, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1025, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1371, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h0, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1502, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1504, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1506, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      rcases p1577_3 (m.d 0 2) (by simp) with h1588 | h1588
                                      · linarith only [h1588, hlam, p1577_0]
                                      · rcases p1577_3 (m.d 1 2) (by simp) with h1590 | h1590
                                        · linarith only [h1502, h1590, hlam]
                                        · rcases p1577_3 (m.d 2 3) (by simp) with h1592 | h1592
                                          · rcases p1577_3 (m.d 2 4) (by simp) with h1593 | h1593
                                            · linarith only [h1520, h1593, hlam]
                                            · linarith only [h1025, h1593, hlam]
                                          · linarith only [h1592, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      rcases p1577_3 (m.d 0 2) (by simp) with h1597 | h1597
                                      · linarith only [h1597, h4, hlam]
                                      · linarith only [h0, h1597, hlam]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1025, h1501, hc02, hc23, hlam, hphi, p1525_1, p1577_1]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h0, h1371, hc12, hc23, hlam, hphi, p1525_1, p1577_1]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      rcases p1577_3 (m.d 0 2) (by simp) with h1603 | h1603
                                      · linarith only [h1603, hlam, p1577_0]
                                      · rcases p1577_3 (m.d 1 2) (by simp) with h1605 | h1605
                                        · linarith only [h1504, h1605, hlam]
                                        · rcases p1577_3 (m.d 2 3) (by simp) with h1607 | h1607
                                          · rcases p1577_3 (m.d 2 4) (by simp) with h1608 | h1608
                                            · rcases p1577_3 (m.d 2 5) (by simp) with h1609 | h1609
                                              · linarith only [h1522, h1609, hlam]
                                              · linarith only [h1371, h1609, hlam]
                                            · linarith only [h1608, hlam, p1577_0]
                                          · linarith only [h1607, h4, hlam]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      rcases p1577_3 (m.d 0 2) (by simp) with h1614 | h1614
                                      · linarith only [h1025, h1614, hlam]
                                      · linarith only [h0, h1614, hlam]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1520, hlam, p1577_1]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h0, h1371, hc12, hc24, hlam, hphi, p1525_1, p1577_1]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      rcases p1577_3 (m.d 0 2) (by simp) with h1620 | h1620
                                      · linarith only [h1620, hlam, p1577_0]
                                      · rcases p1577_3 (m.d 1 2) (by simp) with h1622 | h1622
                                        · linarith only [h1506, h1622, hlam]
                                        · rcases p1577_3 (m.d 2 3) (by simp) with h1624 | h1624
                                          · rcases p1577_3 (m.d 2 4) (by simp) with h1625 | h1625
                                            · rcases p1577_3 (m.d 2 5) (by simp) with h1626 | h1626
                                              · rcases h3bigk with h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1, h1508, hc34, hlam, hphi, ht0b, ht45, ht5b, p1627_1, u0elo0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h4, hlam, p1627_1]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  rcases p1627_3 (m.d 0 3) (by simp) with h1631 | h1631
                                                  · rcases p1627_3 (m.d 1 3) (by simp) with h1632 | h1632
                                                    · linarith only [h1, h1632, hlam]
                                                    · linarith only [h1508, h1632, hlam]
                                                  · linarith only [h1631, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  rcases p1627_3 (m.d 0 3) (by simp) with h1636 | h1636
                                                  · rcases p1627_3 (m.d 1 3) (by simp) with h1637 | h1637
                                                    · linarith only [h1, h1637, hlam]
                                                    · linarith only [h1509, h1637, hlam]
                                                  · linarith only [h1636, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1502, hlam, p1627_1]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p1627_1, u0elo0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1, h1523, hc34, hlam, hphi, ht0b, ht45, ht5b, p1627_1, u0elo0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h0, h1499, h1501, hc12, hc23, hlam, hphi, p1525_1, p1627_1]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  rcases p1627_3 (m.d 0 3) (by simp) with h1647 | h1647
                                                  · linarith only [h1647, h4, hlam]
                                                  · linarith only [h1, h1647, hlam]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  rcases p1627_3 (m.d 0 3) (by simp) with h1651 | h1651
                                                  · linarith only [h1651, h4, hlam]
                                                  · linarith only [h1499, h1651, hlam]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  rcases p1627_3 (m.d 0 3) (by simp) with h1654 | h1654
                                                  · linarith only [h1654, h4, hlam]
                                                  · linarith only [h1500, h1654, hlam]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1499, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1508, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1520, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1523, hlam, p1627_1]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1500, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1509, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1521, hlam, p1627_0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [h1, h1509, hc34, hlam, hphi, ht0b, ht45, ht5b, p1627_1, u0elo0]
                                                · have p1627_0 := h1627c.1
                                                  have p1627_1 := h1627c.2.1
                                                  have p1627_2 := h1627c.2.2.1
                                                  have p1627_3 := h1627c.2.2.2
                                                  linarith only [hlam, p1627_0]
                                              · linarith only [h1626, hlam, p1577_0]
                                            · linarith only [h1025, h1625, hlam]
                                          · linarith only [h1624, h4, hlam]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      rcases p1577_3 (m.d 0 2) (by simp) with h1670 | h1670
                                      · linarith only [h1371, h1670, hlam]
                                      · linarith only [h0, h1670, hlam]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1521, hlam, p1577_1]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [h1522, hlam, p1577_0]
                                    · have p1577_0 := h1577c.1
                                      have p1577_1 := h1577c.2.1
                                      have p1577_2 := h1577c.2.2.1
                                      have p1577_3 := h1577c.2.2.2
                                      linarith only [hlam, p1577_0]
                                  · linarith only [h1371, h1576, hlam]
                                · linarith only [h1025, h1575, hlam]
                              · linarith only [h1574, h4, hlam]
                          · linarith only [h0, h1571, hlam]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1500, hlam, p1525_0]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [h1501, hlam, p1525_1]
                        · have p1525_0 := h1525c.1
                          have p1525_1 := h1525c.2.1
                          have p1525_2 := h1525c.2.2.1
                          have p1525_3 := h1525c.2.2.2
                          linarith only [hlam, p1525_0]
                    · linarith only [h1025, h1501, h1522, hlam]
                  · linarith only [h0, h1509, h1521, h3, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h1499, h1501, h1504, h1510, h1520, h4, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h1500, h1508, h1509, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1687 | h1687
            · linarith only [h1, h1499, h1508, h1687, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1689 | h1689
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1690 | h1690
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1691 | h1691
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1692 | h1692
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1693 | h1693
                      · rcases h0bigk with h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          rcases p1694_3 (m.d 0 1) (by simp) with h1696 | h1696
                          · rcases p1694_3 (m.d 0 2) (by simp) with h1697 | h1697
                            · linarith only [h0, h1697, hlam]
                            · rcases p1694_3 (m.d 0 3) (by simp) with h1699 | h1699
                              · linarith only [h1, h1699, hlam]
                              · linarith only [h1699, h4, hlam]
                          · linarith only [h0, h1696, hlam]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1499, h1508, hc14, hlam, hphi, ht0b, ht45, ht5b, p1694_1, u0elo0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1500, h1501, h1687, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1694_1, u0elo0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1500, h1687, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1694_1, u0elo0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h0, hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h4, hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1025, hlam, p1694_1]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1371, hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1, hlam, p1694_1]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          rcases p1694_3 (m.d 0 1) (by simp) with h1712 | h1712
                          · rcases p1694_3 (m.d 0 2) (by simp) with h1713 | h1713
                            · linarith only [h1713, h4, hlam]
                            · rcases p1694_3 (m.d 0 3) (by simp) with h1715 | h1715
                              · rcases p1694_3 (m.d 0 4) (by simp) with h1716 | h1716
                                · linarith only [h1499, h1716, hlam]
                                · linarith only [h1025, h1716, hlam]
                              · linarith only [h1715, h4, hlam]
                          · linarith only [h0, h1712, hlam]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1, h1500, h1501, h1502, h1687, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1694_1, u0elo0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1, h1500, h1502, h1687, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1694_1, u0elo0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h2, hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          rcases p1694_3 (m.d 0 1) (by simp) with h1725 | h1725
                          · rcases p1694_3 (m.d 0 2) (by simp) with h1726 | h1726
                            · linarith only [h1025, h1726, hlam]
                            · rcases p1694_3 (m.d 0 3) (by simp) with h1728 | h1728
                              · rcases p1694_3 (m.d 0 4) (by simp) with h1729 | h1729
                                · rcases p1694_3 (m.d 0 5) (by simp) with h1730 | h1730
                                  · linarith only [h1501, h1730, hlam]
                                  · linarith only [h1371, h1730, hlam]
                                · linarith only [h1025, h1729, hlam]
                              · linarith only [h1728, h4, hlam]
                          · linarith only [h0, h1725, hlam]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1499, hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1, h1499, h1500, h1502, h1687, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1694_1, u0elo0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h3, hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          rcases p1694_3 (m.d 0 1) (by simp) with h1740 | h1740
                          · rcases p1694_3 (m.d 0 2) (by simp) with h1741 | h1741
                            · linarith only [h1371, h1741, hlam]
                            · rcases p1694_3 (m.d 0 3) (by simp) with h1743 | h1743
                              · rcases p1694_3 (m.d 0 4) (by simp) with h1744 | h1744
                                · rcases p1694_3 (m.d 0 5) (by simp) with h1745 | h1745
                                  · rcases h2bigk with h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c | h1746c
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1, h1499, h1501, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1694_1, p1746_1, u0elo0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h4, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1025, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1371, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h0, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1502, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1504, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1506, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      rcases p1746_3 (m.d 0 2) (by simp) with h1757 | h1757
                                      · linarith only [h1757, hlam, p1746_0]
                                      · rcases p1746_3 (m.d 1 2) (by simp) with h1759 | h1759
                                        · linarith only [h1502, h1759, hlam]
                                        · rcases p1746_3 (m.d 2 3) (by simp) with h1761 | h1761
                                          · rcases p1746_3 (m.d 2 4) (by simp) with h1762 | h1762
                                            · linarith only [h1690, h1762, hlam]
                                            · linarith only [h1025, h1762, hlam]
                                          · linarith only [h1761, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      rcases p1746_3 (m.d 0 2) (by simp) with h1766 | h1766
                                      · linarith only [h1766, h4, hlam]
                                      · linarith only [h0, h1766, hlam]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1025, h1501, hc02, hc23, hlam, hphi, p1694_1, p1746_1]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h0, h1371, hc12, hc23, hlam, hphi, p1694_1, p1746_1]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      rcases p1746_3 (m.d 0 2) (by simp) with h1772 | h1772
                                      · linarith only [h1772, hlam, p1746_0]
                                      · rcases p1746_3 (m.d 1 2) (by simp) with h1774 | h1774
                                        · linarith only [h1504, h1774, hlam]
                                        · rcases p1746_3 (m.d 2 3) (by simp) with h1776 | h1776
                                          · rcases p1746_3 (m.d 2 4) (by simp) with h1777 | h1777
                                            · rcases p1746_3 (m.d 2 5) (by simp) with h1778 | h1778
                                              · linarith only [h1692, h1778, hlam]
                                              · linarith only [h1371, h1778, hlam]
                                            · linarith only [h1777, hlam, p1746_0]
                                          · linarith only [h1776, h4, hlam]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      rcases p1746_3 (m.d 0 2) (by simp) with h1783 | h1783
                                      · linarith only [h1025, h1783, hlam]
                                      · linarith only [h0, h1783, hlam]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1690, hlam, p1746_1]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h0, h1371, hc12, hc24, hlam, hphi, p1694_1, p1746_1]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      rcases p1746_3 (m.d 0 2) (by simp) with h1789 | h1789
                                      · linarith only [h1789, hlam, p1746_0]
                                      · rcases p1746_3 (m.d 1 2) (by simp) with h1791 | h1791
                                        · linarith only [h1506, h1791, hlam]
                                        · rcases p1746_3 (m.d 2 3) (by simp) with h1793 | h1793
                                          · rcases p1746_3 (m.d 2 4) (by simp) with h1794 | h1794
                                            · rcases p1746_3 (m.d 2 5) (by simp) with h1795 | h1795
                                              · rcases h3bigk with h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  rcases p1796_3 (m.d 0 3) (by simp) with h1798 | h1798
                                                  · rcases p1796_3 (m.d 1 3) (by simp) with h1799 | h1799
                                                    · linarith only [h1, h1799, hlam]
                                                    · rcases p1796_3 (m.d 2 3) (by simp) with h1801 | h1801
                                                      · rcases p1796_3 (m.d 3 4) (by simp) with h1802 | h1802
                                                        · linarith only [h1499, h1802, hlam]
                                                        · linarith only [h1508, h1802, hlam]
                                                      · linarith only [h1502, h1801, hlam]
                                                  · linarith only [h1, h1798, hlam]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h4, hlam, p1796_1]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1, h1502, h1687, h1693, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1796_1, u0elo0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1, h1502, h1687, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1796_1, u0elo0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1, hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1502, hlam, p1796_1]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1508, hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1687, hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1499, h1501, hc02, hc23, hlam, hphi, p1694_1, p1796_1]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  rcases p1796_3 (m.d 0 3) (by simp) with h1816 | h1816
                                                  · linarith only [h1816, h4, hlam]
                                                  · linarith only [h1, h1816, hlam]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1502, h1687, h1693, hc12, hc23, hlam, hphi, p1796_1]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1502, h1687, hc12, hc23, hlam, hphi, p1796_1]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1499, hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1, h1499, h1502, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1796_1, u0elo0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1690, hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1, h1499, h1502, h1687, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1796_1, u0elo0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1500, hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1, h1500, h1502, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1796_1, u0elo0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1691, hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [h1693, hlam, p1796_0]
                                                · have p1796_0 := h1796c.1
                                                  have p1796_1 := h1796c.2.1
                                                  have p1796_2 := h1796c.2.2.1
                                                  have p1796_3 := h1796c.2.2.2
                                                  linarith only [hlam, p1796_0]
                                              · linarith only [h1795, hlam, p1746_0]
                                            · linarith only [h1025, h1794, hlam]
                                          · linarith only [h1793, h4, hlam]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      rcases p1746_3 (m.d 0 2) (by simp) with h1835 | h1835
                                      · linarith only [h1371, h1835, hlam]
                                      · linarith only [h0, h1835, hlam]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1691, hlam, p1746_1]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [h1692, hlam, p1746_0]
                                    · have p1746_0 := h1746c.1
                                      have p1746_1 := h1746c.2.1
                                      have p1746_2 := h1746c.2.2.1
                                      have p1746_3 := h1746c.2.2.2
                                      linarith only [hlam, p1746_0]
                                  · linarith only [h1371, h1745, hlam]
                                · linarith only [h1025, h1744, hlam]
                              · linarith only [h1743, h4, hlam]
                          · linarith only [h0, h1740, hlam]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1500, hlam, p1694_0]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [h1501, hlam, p1694_1]
                        · have p1694_0 := h1694c.1
                          have p1694_1 := h1694c.2.1
                          have p1694_2 := h1694c.2.2.1
                          have p1694_3 := h1694c.2.2.2
                          linarith only [hlam, p1694_0]
                      · linarith only [h1689, h1693, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h1, h1499, h1508, h1689, h1692, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1500, h1691, h4, hlam]
                · linarith only [h1499, h1690, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1852 | h1852
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1853 | h1853
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1854 | h1854
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1855 | h1855
                      · linarith only [h1, h1499, h1689, h1855, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h1499, h1501, h1502, h1508, h1855, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1025, h1501, h1854, hlam]
                  · linarith only [h1500, h1853, h4, hlam]
                · linarith only [h1499, h1852, h4, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1861 | h1861
    · linarith only [h0, h1499, h1861, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1863 | h1863
      · linarith only [h0, h1025, h1863, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1865 | h1865
        · linarith only [h0, h1371, h1865, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1867 | h1867
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1868 | h1868
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1869 | h1869
              · linarith only [h1501, h1869, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1871 | h1871
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1872 | h1872
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1873 | h1873
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1874 | h1874
                      · linarith only [h1, h1025, h1501, h1867, h1874, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          rcases p1876_3 (m.d 0 1) (by simp) with h1878 | h1878
                          · rcases p1876_3 (m.d 0 2) (by simp) with h1879 | h1879
                            · linarith only [h0, h1879, hlam]
                            · rcases p1876_3 (m.d 0 3) (by simp) with h1881 | h1881
                              · linarith only [h1, h1881, hlam]
                              · linarith only [h1881, h4, hlam]
                          · linarith only [h0, h1878, hlam]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h1, h1868, hc35, hlam, hphi, ht0b, ht5b, p1876_1, u0elo0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          rcases p1876_3 (m.d 0 1) (by simp) with h1886 | h1886
                          · rcases p1876_3 (m.d 0 2) (by simp) with h1887 | h1887
                            · linarith only [h0, h1887, hlam]
                            · rcases p1876_3 (m.d 0 3) (by simp) with h1889 | h1889
                              · linarith only [h1, h1889, hlam]
                              · linarith only [h1499, h1889, hlam]
                          · linarith only [h1886, h2, hlam]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          rcases p1876_3 (m.d 0 1) (by simp) with h1893 | h1893
                          · rcases p1876_3 (m.d 0 2) (by simp) with h1894 | h1894
                            · linarith only [h0, h1894, hlam]
                            · rcases p1876_3 (m.d 0 3) (by simp) with h1896 | h1896
                              · linarith only [h1, h1896, hlam]
                              · linarith only [h1500, h1896, hlam]
                          · linarith only [h1893, h3, hlam]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h0, hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h4, hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h1025, hlam, p1876_1]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h1371, hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h1, hlam, p1876_1]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          rcases p1876_3 (m.d 0 1) (by simp) with h1906 | h1906
                          · rcases p1876_3 (m.d 0 2) (by simp) with h1907 | h1907
                            · linarith only [h1907, h4, hlam]
                            · rcases p1876_3 (m.d 0 3) (by simp) with h1909 | h1909
                              · rcases p1876_3 (m.d 0 4) (by simp) with h1910 | h1910
                                · linarith only [h1499, h1910, hlam]
                                · linarith only [h1025, h1910, hlam]
                              · linarith only [h1909, h4, hlam]
                          · linarith only [h0, h1906, hlam]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          rcases p1876_3 (m.d 0 1) (by simp) with h1916 | h1916
                          · rcases p1876_3 (m.d 0 2) (by simp) with h1917 | h1917
                            · linarith only [h1917, h4, hlam]
                            · rcases p1876_3 (m.d 0 3) (by simp) with h1919 | h1919
                              · rcases p1876_3 (m.d 0 4) (by simp) with h1920 | h1920
                                · linarith only [h1499, h1920, hlam]
                                · rcases p1876_3 (m.d 0 5) (by simp) with h1922 | h1922
                                  · linarith only [h1500, h1922, hlam]
                                  · linarith only [h1501, h1922, hlam]
                              · linarith only [h1499, h1919, hlam]
                          · linarith only [h1916, h2, hlam]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          rcases p1876_3 (m.d 0 1) (by simp) with h1927 | h1927
                          · rcases p1876_3 (m.d 0 2) (by simp) with h1928 | h1928
                            · linarith only [h1928, h4, hlam]
                            · rcases p1876_3 (m.d 0 3) (by simp) with h1930 | h1930
                              · rcases p1876_3 (m.d 0 4) (by simp) with h1931 | h1931
                                · linarith only [h1499, h1931, hlam]
                                · rcases p1876_3 (m.d 0 5) (by simp) with h1933 | h1933
                                  · linarith only [h1500, h1933, hlam]
                                  · rcases h2bigk with h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c | h1935c
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p1935_1]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h4, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1025, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1371, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h0, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1861, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1863, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1865, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      rcases p1935_3 (m.d 0 2) (by simp) with h1946 | h1946
                                      · linarith only [h1946, hlam, p1935_0]
                                      · rcases p1935_3 (m.d 1 2) (by simp) with h1948 | h1948
                                        · linarith only [h1861, h1948, hlam]
                                        · rcases p1935_3 (m.d 2 3) (by simp) with h1950 | h1950
                                          · rcases p1935_3 (m.d 2 4) (by simp) with h1951 | h1951
                                            · linarith only [h1871, h1951, hlam]
                                            · linarith only [h1025, h1951, hlam]
                                          · linarith only [h1950, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      rcases p1935_3 (m.d 0 2) (by simp) with h1955 | h1955
                                      · linarith only [h1955, h4, hlam]
                                      · linarith only [h0, h1955, hlam]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1025, hc02, hc23, hlam, hphi, p1935_1]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h0, h1371, hc12, hc23, hlam, hphi, p1935_1]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      rcases p1935_3 (m.d 0 2) (by simp) with h1961 | h1961
                                      · linarith only [h1961, hlam, p1935_0]
                                      · rcases p1935_3 (m.d 1 2) (by simp) with h1963 | h1963
                                        · linarith only [h1863, h1963, hlam]
                                        · rcases p1935_3 (m.d 2 3) (by simp) with h1965 | h1965
                                          · rcases p1935_3 (m.d 2 4) (by simp) with h1966 | h1966
                                            · rcases p1935_3 (m.d 2 5) (by simp) with h1967 | h1967
                                              · linarith only [h1873, h1967, hlam]
                                              · linarith only [h1371, h1967, hlam]
                                            · linarith only [h1966, hlam, p1935_0]
                                          · linarith only [h1965, h4, hlam]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      rcases p1935_3 (m.d 0 2) (by simp) with h1972 | h1972
                                      · linarith only [h1025, h1972, hlam]
                                      · linarith only [h0, h1972, hlam]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1871, hlam, p1935_1]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1501, h1863, h1873, h2, hc12, hc24, hlam, hphi, p1935_1]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      rcases p1935_3 (m.d 0 2) (by simp) with h1978 | h1978
                                      · linarith only [h1978, hlam, p1935_0]
                                      · rcases p1935_3 (m.d 1 2) (by simp) with h1980 | h1980
                                        · linarith only [h1865, h1980, hlam]
                                        · rcases p1935_3 (m.d 2 3) (by simp) with h1982 | h1982
                                          · rcases p1935_3 (m.d 2 4) (by simp) with h1983 | h1983
                                            · rcases p1935_3 (m.d 2 5) (by simp) with h1984 | h1984
                                              · rcases h3bigk with h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c | h1985c
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1, h1868, h1874, hc34, hlam, hphi, ht0b, ht45, ht5b, p1985_1, u0elo0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h4, hlam, p1985_1]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  rcases p1985_3 (m.d 0 3) (by simp) with h1989 | h1989
                                                  · rcases p1985_3 (m.d 1 3) (by simp) with h1990 | h1990
                                                    · linarith only [h1, h1990, hlam]
                                                    · linarith only [h1867, h1990, hlam]
                                                  · linarith only [h1989, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  rcases p1985_3 (m.d 0 3) (by simp) with h1994 | h1994
                                                  · rcases p1985_3 (m.d 1 3) (by simp) with h1995 | h1995
                                                    · linarith only [h1, h1995, hlam]
                                                    · linarith only [h1868, h1995, hlam]
                                                  · linarith only [h1994, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1861, hlam, p1985_1]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p1985_1, u0elo0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1, h1874, hc34, hlam, hphi, ht0b, ht45, ht5b, p1985_1, u0elo0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1876_1, p1985_1]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  rcases p1985_3 (m.d 0 3) (by simp) with h2005 | h2005
                                                  · linarith only [h2005, h4, hlam]
                                                  · linarith only [h1, h2005, hlam]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  rcases p1985_3 (m.d 0 3) (by simp) with h2009 | h2009
                                                  · linarith only [h2009, h4, hlam]
                                                  · linarith only [h1499, h2009, hlam]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  rcases p1985_3 (m.d 0 3) (by simp) with h2012 | h2012
                                                  · linarith only [h2012, h4, hlam]
                                                  · linarith only [h1500, h2012, hlam]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1499, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1867, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1871, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1874, hlam, p1985_1]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1500, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1868, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1872, hlam, p1985_0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [h1, h1868, hc34, hlam, hphi, ht0b, ht45, ht5b, p1985_1, u0elo0]
                                                · have p1985_0 := h1985c.1
                                                  have p1985_1 := h1985c.2.1
                                                  have p1985_2 := h1985c.2.2.1
                                                  have p1985_3 := h1985c.2.2.2
                                                  linarith only [hlam, p1985_0]
                                              · linarith only [h1984, hlam, p1935_0]
                                            · linarith only [h1025, h1983, hlam]
                                          · linarith only [h1982, h4, hlam]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      rcases p1935_3 (m.d 0 2) (by simp) with h2028 | h2028
                                      · linarith only [h1371, h2028, hlam]
                                      · linarith only [h0, h2028, hlam]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1872, hlam, p1935_1]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [h1873, hlam, p1935_0]
                                    · have p1935_0 := h1935c.1
                                      have p1935_1 := h1935c.2.1
                                      have p1935_2 := h1935c.2.2.1
                                      have p1935_3 := h1935c.2.2.2
                                      linarith only [hlam, p1935_0]
                              · linarith only [h1500, h1930, hlam]
                          · linarith only [h1927, h3, hlam]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h2, hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h0, h1501, hc12, hc45, hlam, hphi, ht23, ht34, p1876_1]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h1499, hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h1501, hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h3, hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h0, h1501, h1871, h1873, hc12, hc23, hlam, hphi, p1876_1]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h1500, hlam, p1876_0]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [h1501, h1863, h1871, h1873, h2, hc12, hc23, hlam, hphi, p1876_1]
                        · have p1876_0 := h1876c.1
                          have p1876_1 := h1876c.2.1
                          have p1876_2 := h1876c.2.2.1
                          have p1876_3 := h1876c.2.2.2
                          linarith only [hlam, p1876_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2046 | h2046
                      · linarith only [h0, h1025, h1873, h2046, hc12, hc34, hlam, hphi, ht23]
                      · rcases h0bigk with h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c | h2048c
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          rcases p2048_3 (m.d 0 1) (by simp) with h2050 | h2050
                          · rcases p2048_3 (m.d 0 2) (by simp) with h2051 | h2051
                            · linarith only [h0, h2051, hlam]
                            · rcases p2048_3 (m.d 0 3) (by simp) with h2053 | h2053
                              · linarith only [h1, h2053, hlam]
                              · linarith only [h2053, h4, hlam]
                          · linarith only [h0, h2050, hlam]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h1499, hc34, hlam, hphi, ht0b, ht45, ht5b, p2048_1, u0elo0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          rcases p2048_3 (m.d 0 1) (by simp) with h2058 | h2058
                          · rcases p2048_3 (m.d 0 2) (by simp) with h2059 | h2059
                            · linarith only [h0, h2059, hlam]
                            · rcases p2048_3 (m.d 0 3) (by simp) with h2061 | h2061
                              · linarith only [h1, h2061, hlam]
                              · linarith only [h1499, h2061, hlam]
                          · linarith only [h2, h2058, hlam]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          rcases p2048_3 (m.d 0 1) (by simp) with h2065 | h2065
                          · rcases p2048_3 (m.d 0 2) (by simp) with h2066 | h2066
                            · linarith only [h0, h2066, hlam]
                            · rcases p2048_3 (m.d 0 3) (by simp) with h2068 | h2068
                              · linarith only [h1, h2068, hlam]
                              · linarith only [h1500, h2068, hlam]
                          · linarith only [h2065, h3, hlam]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h0, hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h4, hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h1025, hlam, p2048_1]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h1371, hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h1, hlam, p2048_1]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          rcases p2048_3 (m.d 0 1) (by simp) with h2078 | h2078
                          · rcases p2048_3 (m.d 0 2) (by simp) with h2079 | h2079
                            · linarith only [h2079, h4, hlam]
                            · rcases p2048_3 (m.d 0 3) (by simp) with h2081 | h2081
                              · rcases p2048_3 (m.d 0 4) (by simp) with h2082 | h2082
                                · linarith only [h1499, h2082, hlam]
                                · linarith only [h1025, h2082, hlam]
                              · linarith only [h2081, h4, hlam]
                          · linarith only [h0, h2078, hlam]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          rcases p2048_3 (m.d 0 1) (by simp) with h2088 | h2088
                          · rcases p2048_3 (m.d 0 2) (by simp) with h2089 | h2089
                            · linarith only [h2089, h4, hlam]
                            · rcases p2048_3 (m.d 0 3) (by simp) with h2091 | h2091
                              · rcases p2048_3 (m.d 0 4) (by simp) with h2092 | h2092
                                · linarith only [h1499, h2092, hlam]
                                · rcases p2048_3 (m.d 0 5) (by simp) with h2094 | h2094
                                  · linarith only [h1500, h2094, hlam]
                                  · linarith only [h1501, h2094, hlam]
                              · linarith only [h1499, h2091, hlam]
                          · linarith only [h2, h2088, hlam]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          rcases p2048_3 (m.d 0 1) (by simp) with h2099 | h2099
                          · rcases p2048_3 (m.d 0 2) (by simp) with h2100 | h2100
                            · linarith only [h2100, h4, hlam]
                            · rcases p2048_3 (m.d 0 3) (by simp) with h2102 | h2102
                              · rcases p2048_3 (m.d 0 4) (by simp) with h2103 | h2103
                                · linarith only [h1499, h2103, hlam]
                                · rcases p2048_3 (m.d 0 5) (by simp) with h2105 | h2105
                                  · linarith only [h1500, h2105, hlam]
                                  · rcases h2bigk with h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c | h2107c
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1025, hc12, hc24, hlam, hphi, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h4, hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1025, hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1371, hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h0, hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1861, hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1863, hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1865, hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      rcases p2107_3 (m.d 0 2) (by simp) with h2118 | h2118
                                      · linarith only [h2118, hlam, p2107_0]
                                      · rcases p2107_3 (m.d 1 2) (by simp) with h2120 | h2120
                                        · linarith only [h1861, h2120, hlam]
                                        · rcases p2107_3 (m.d 2 3) (by simp) with h2122 | h2122
                                          · rcases p2107_3 (m.d 2 4) (by simp) with h2123 | h2123
                                            · linarith only [h1871, h2123, hlam]
                                            · linarith only [h1025, h2123, hlam]
                                          · linarith only [h2122, hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      rcases p2107_3 (m.d 0 2) (by simp) with h2127 | h2127
                                      · linarith only [h2127, h4, hlam]
                                      · linarith only [h0, h2127, hlam]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1025, hc02, hc23, hlam, hphi, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h0, h1371, hc12, hc23, hlam, hphi, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h0, h1873, hc12, hc45, hlam, hphi, ht23, ht34, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1873, hc12, hc45, hlam, hphi, ht23, ht34, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1871, hlam, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [hlam, p2107_0]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1873, hlam, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      rcases p2107_3 (m.d 0 2) (by simp) with h2138 | h2138
                                      · linarith only [h2138, hlam, p2107_0]
                                      · rcases p2107_3 (m.d 1 2) (by simp) with h2140 | h2140
                                        · linarith only [h1865, h2140, hlam]
                                        · rcases p2107_3 (m.d 2 3) (by simp) with h2142 | h2142
                                          · rcases p2107_3 (m.d 2 4) (by simp) with h2143 | h2143
                                            · linarith only [h1873, h2143, hlam]
                                            · linarith only [h1025, h2143, hlam]
                                          · linarith only [h2142, h4, hlam]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      rcases p2107_3 (m.d 0 2) (by simp) with h2147 | h2147
                                      · linarith only [h1371, h2147, hlam]
                                      · linarith only [h0, h2147, hlam]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h1872, hlam, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [h0, h1025, hc12, hc25, hlam, hphi, p2107_1]
                                    · have p2107_0 := h2107c.1
                                      have p2107_1 := h2107c.2.1
                                      have p2107_2 := h2107c.2.2.1
                                      have p2107_3 := h2107c.2.2.2
                                      linarith only [hlam, p2107_0]
                              · linarith only [h1500, h2102, hlam]
                          · linarith only [h2099, h3, hlam]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h2, hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h0, h1501, hc12, hc45, hlam, hphi, ht23, ht34, p2048_1]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h1499, hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h1501, hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h3, hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          rcases p2048_3 (m.d 0 1) (by simp) with h2161 | h2161
                          · rcases p2048_3 (m.d 0 2) (by simp) with h2162 | h2162
                            · linarith only [h1371, h2162, hlam]
                            · rcases p2048_3 (m.d 0 3) (by simp) with h2164 | h2164
                              · rcases p2048_3 (m.d 0 4) (by simp) with h2165 | h2165
                                · linarith only [h1501, h2165, hlam]
                                · linarith only [h1025, h2165, hlam]
                              · linarith only [h2164, h4, hlam]
                          · linarith only [h0, h2161, hlam]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [h1500, hlam, p2048_0]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          rcases p2048_3 (m.d 0 1) (by simp) with h2171 | h2171
                          · rcases p2048_3 (m.d 0 2) (by simp) with h2172 | h2172
                            · linarith only [h1371, h2172, hlam]
                            · rcases p2048_3 (m.d 0 3) (by simp) with h2174 | h2174
                              · rcases p2048_3 (m.d 0 4) (by simp) with h2175 | h2175
                                · linarith only [h1501, h2175, hlam]
                                · rcases p2048_3 (m.d 0 5) (by simp) with h2177 | h2177
                                  · rcases h2bigk with h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h4, hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1025, hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1371, hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h0, hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1861, hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1863, hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1865, hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      rcases p2178_3 (m.d 0 2) (by simp) with h2189 | h2189
                                      · linarith only [h2189, hlam, p2178_0]
                                      · rcases p2178_3 (m.d 1 2) (by simp) with h2191 | h2191
                                        · linarith only [h1861, h2191, hlam]
                                        · rcases p2178_3 (m.d 2 3) (by simp) with h2193 | h2193
                                          · rcases p2178_3 (m.d 2 4) (by simp) with h2194 | h2194
                                            · linarith only [h1871, h2194, hlam]
                                            · linarith only [h1025, h2194, hlam]
                                          · linarith only [h2193, hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      rcases p2178_3 (m.d 0 2) (by simp) with h2198 | h2198
                                      · linarith only [h2198, h4, hlam]
                                      · linarith only [h0, h2198, hlam]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1025, hc02, hc23, hlam, hphi, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h0, h1371, hc12, hc23, hlam, hphi, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h0, h1873, hc12, hc45, hlam, hphi, ht23, ht34, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1873, hc12, hc45, hlam, hphi, ht23, ht34, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1871, hlam, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [hlam, p2178_0]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1873, hlam, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      rcases p2178_3 (m.d 0 2) (by simp) with h2209 | h2209
                                      · linarith only [h2209, hlam, p2178_0]
                                      · rcases p2178_3 (m.d 1 2) (by simp) with h2211 | h2211
                                        · linarith only [h1865, h2211, hlam]
                                        · rcases p2178_3 (m.d 2 3) (by simp) with h2213 | h2213
                                          · rcases p2178_3 (m.d 2 4) (by simp) with h2214 | h2214
                                            · linarith only [h1873, h2214, hlam]
                                            · linarith only [h1025, h2214, hlam]
                                          · linarith only [h2213, h4, hlam]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      rcases p2178_3 (m.d 0 2) (by simp) with h2218 | h2218
                                      · linarith only [h1371, h2218, hlam]
                                      · linarith only [h0, h2218, hlam]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h1872, hlam, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [h0, h1025, hc12, hc25, hlam, hphi, p2178_1]
                                    · have p2178_0 := h2178c.1
                                      have p2178_1 := h2178c.2.1
                                      have p2178_2 := h2178c.2.2.1
                                      have p2178_3 := h2178c.2.2.2
                                      linarith only [hlam, p2178_0]
                                  · linarith only [h1501, h2177, hlam]
                              · linarith only [h1499, h2174, hlam]
                          · linarith only [h2, h2171, hlam]
                        · have p2048_0 := h2048c.1
                          have p2048_1 := h2048c.2.1
                          have p2048_2 := h2048c.2.2.1
                          have p2048_3 := h2048c.2.2.2
                          linarith only [hlam, p2048_0]
                  · linarith only [h1, h1868, h1872, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h1499, h1871, h4, hlam]
            · linarith only [h1500, h1867, h1868, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2231 | h2231
            · linarith only [h1, h1499, h1867, h2231, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2233 | h2233
              · linarith only [h1501, h2, h2233, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2235 | h2235
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2236 | h2236
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2237 | h2237
                    · linarith only [h1499, h1501, h1861, h1867, h2237, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2239 | h2239
                      · linarith only [h1499, h2237, h2239, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c | h2241c
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          rcases p2241_3 (m.d 0 1) (by simp) with h2243 | h2243
                          · rcases p2241_3 (m.d 0 2) (by simp) with h2244 | h2244
                            · linarith only [h0, h2244, hlam]
                            · rcases p2241_3 (m.d 0 3) (by simp) with h2246 | h2246
                              · linarith only [h1, h2246, hlam]
                              · linarith only [h2246, h4, hlam]
                          · linarith only [h0, h2243, hlam]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1500, h1861, h1867, h2239, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2241_1, u0elo0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1499, h1861, h1867, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2241_1, u0elo0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1500, h1861, h1867, h2239, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2241_1, u0elo0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h0, hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h4, hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1025, hlam, p2241_1]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1371, hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1, hlam, p2241_1]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          rcases p2241_3 (m.d 0 1) (by simp) with h2259 | h2259
                          · rcases p2241_3 (m.d 0 2) (by simp) with h2260 | h2260
                            · linarith only [h2260, h4, hlam]
                            · rcases p2241_3 (m.d 0 3) (by simp) with h2262 | h2262
                              · rcases p2241_3 (m.d 0 4) (by simp) with h2263 | h2263
                                · linarith only [h1499, h2263, hlam]
                                · linarith only [h1025, h2263, hlam]
                              · linarith only [h2262, h4, hlam]
                          · linarith only [h0, h2259, hlam]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1499, h1861, h1867, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2241_1, u0elo2]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1, h1500, h1861, h1867, h2239, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2241_1, u0elo0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h2, hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h0, h1025, h2237, hc12, hc45, hlam, hphi, ht23, ht34, p2241_1]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1499, hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1501, hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h3, hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          rcases p2241_3 (m.d 0 1) (by simp) with h2277 | h2277
                          · rcases p2241_3 (m.d 0 2) (by simp) with h2278 | h2278
                            · linarith only [h1371, h2278, hlam]
                            · rcases p2241_3 (m.d 0 3) (by simp) with h2280 | h2280
                              · rcases p2241_3 (m.d 0 4) (by simp) with h2281 | h2281
                                · linarith only [h1501, h2281, hlam]
                                · linarith only [h1025, h2281, hlam]
                              · linarith only [h2280, h4, hlam]
                          · linarith only [h0, h2277, hlam]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1500, hlam, p2241_0]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [h1499, h1861, h1867, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2241_1, u0elo4]
                        · have p2241_0 := h2241c.1
                          have p2241_1 := h2241c.2.1
                          have p2241_2 := h2241c.2.2.1
                          have p2241_3 := h2241c.2.2.2
                          linarith only [hlam, p2241_0]
                  · linarith only [h1499, h1861, h1867, h2236, h4, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1499, h2235, h4, hlam]

end R2N4
