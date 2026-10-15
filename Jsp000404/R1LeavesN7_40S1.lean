import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1488 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1489 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1490 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1491 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h1492 | h1492
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1493 | h1493
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1494 | h1494
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1495 | h1495
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1496 | h1496
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1497 | h1497
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1498 | h1498
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1499 | h1499
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1500 | h1500
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1501 | h1501
                    · rcases h1bigk with h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h0, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h927, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1241, h1497, hlam, p1502_1]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1241, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        rcases p1502_3 (m.d 0 1) (by simp) with h1508 | h1508
                        · linarith only [h1508, hlam, p1502_0]
                        · rcases p1502_3 (m.d 1 2) (by simp) with h1510 | h1510
                          · rcases p1502_3 (m.d 1 3) (by simp) with h1511 | h1511
                            · linarith only [h1492, h1511, hlam]
                            · linarith only [h1511, h927, hlam]
                          · linarith only [h1510, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h927, hc01, hc12, hlam, hphi, p1502_1]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1241, h1497, hc01, hc12, hlam, hphi, p1502_1]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1241, hc01, hc12, hlam, hphi, p1502_1]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        rcases p1502_3 (m.d 0 1) (by simp) with h1519 | h1519
                        · linarith only [h1519, hlam, p1502_0]
                        · rcases p1502_3 (m.d 1 2) (by simp) with h1521 | h1521
                          · rcases p1502_3 (m.d 1 3) (by simp) with h1522 | h1522
                            · rcases p1502_3 (m.d 1 4) (by simp) with h1523 | h1523
                              · linarith only [h1495, h1523, hlam]
                              · linarith only [h1241, h1497, h1523, hlam]
                            · linarith only [h1522, hlam, p1502_0]
                          · linarith only [h0, h1521, hlam]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1492, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1241, h1497, hc01, hc13, hlam, hphi, p1502_1]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1241, h1492, hc01, hc12, hlam, hphi, p1502_1]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        rcases p1502_3 (m.d 0 1) (by simp) with h1532 | h1532
                        · linarith only [h1532, hlam, p1502_0]
                        · rcases p1502_3 (m.d 1 2) (by simp) with h1534 | h1534
                          · rcases p1502_3 (m.d 1 3) (by simp) with h1535 | h1535
                            · rcases p1502_3 (m.d 1 4) (by simp) with h1536 | h1536
                              · rcases p1502_3 (m.d 1 5) (by simp) with h1537 | h1537
                                · linarith only [h1497, h1537, hlam]
                                · linarith only [h1241, h1537, hlam]
                              · linarith only [h1536, hlam, p1502_0]
                            · linarith only [h1535, h927, hlam]
                          · linarith only [h0, h1534, hlam]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1493, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1495, hlam, p1502_1]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1241, hc01, hc14, hlam, hphi, p1502_1]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        rcases p1502_3 (m.d 0 1) (by simp) with h1547 | h1547
                        · linarith only [h1547, hlam, p1502_0]
                        · rcases p1502_3 (m.d 1 2) (by simp) with h1549 | h1549
                          · rcases p1502_3 (m.d 1 3) (by simp) with h1550 | h1550
                            · rcases p1502_3 (m.d 1 4) (by simp) with h1551 | h1551
                              · rcases p1502_3 (m.d 1 5) (by simp) with h1552 | h1552
                                · rcases h5bigk with h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1241, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1553_1, u2ehi4]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    rcases p1553_3 (m.d 0 5) (by simp) with h1557 | h1557
                                    · rcases p1553_3 (m.d 1 5) (by simp) with h1558 | h1558
                                      · rcases p1553_3 (m.d 2 5) (by simp) with h1559 | h1559
                                        · linarith only [h1488, h1559, hlam]
                                        · linarith only [h1499, h1559, hlam]
                                      · linarith only [h1496, h1558, hlam]
                                    · linarith only [h1490, h1557, hlam]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    rcases p1553_3 (m.d 0 5) (by simp) with h1564 | h1564
                                    · rcases p1553_3 (m.d 1 5) (by simp) with h1565 | h1565
                                      · rcases p1553_3 (m.d 2 5) (by simp) with h1566 | h1566
                                        · linarith only [h1488, h1566, hlam]
                                        · linarith only [h1500, h1566, hlam]
                                      · linarith only [h1497, h1565, hlam]
                                    · linarith only [h1491, h1564, hlam]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1241, h1492, h1495, h1497, hc01, hc12, hlam, hphi, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1492, h1495, h1497, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1553_1, u2ehi4]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    rcases p1553_3 (m.d 0 5) (by simp) with h1574 | h1574
                                    · linarith only [h1241, h1574, hlam]
                                    · linarith only [h1490, h1574, hlam]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    rcases p1553_3 (m.d 0 5) (by simp) with h1577 | h1577
                                    · linarith only [h1241, h1577, hlam]
                                    · linarith only [h1491, h1577, hlam]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1488, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1494, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1488, h1501, hc02, hc45, hlam, hphi, ht0b, ht5b, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h0, h1486, h1498, h1500, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1490, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1496, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1499, hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1490, hc03, hc45, hlam, hphi, ht0b, ht5b, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1491, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1497, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1500, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [h1501, hlam, p1553_1]
                                  · have p1553_0 := h1553c.1
                                    have p1553_1 := h1553c.2.1
                                    have p1553_2 := h1553c.2.2.1
                                    have p1553_3 := h1553c.2.2.2
                                    linarith only [hlam, p1553_0]
                                · linarith only [h1552, hlam, p1502_0]
                              · linarith only [h1497, h1551, hlam, p1502_1]
                            · linarith only [h1550, h927, hlam]
                          · linarith only [h0, h1549, hlam]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1494, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1496, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [h1497, hlam, p1502_0]
                      · have p1502_0 := h1502c.1
                        have p1502_1 := h1502c.2.1
                        have p1502_2 := h1502c.2.2.1
                        have p1502_3 := h1502c.2.2.2
                        linarith only [hlam, p1502_0]
                    · rcases h1bigk with h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h0, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h927, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1241, h1497, hlam, p1603_1]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1241, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        rcases p1603_3 (m.d 0 1) (by simp) with h1609 | h1609
                        · linarith only [h1609, hlam, p1603_0]
                        · rcases p1603_3 (m.d 1 2) (by simp) with h1611 | h1611
                          · rcases p1603_3 (m.d 1 3) (by simp) with h1612 | h1612
                            · linarith only [h1492, h1612, hlam]
                            · linarith only [h1612, h927, hlam]
                          · linarith only [h1611, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h927, hc01, hc12, hlam, hphi, p1603_1]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1241, h1497, hc01, hc12, hlam, hphi, p1603_1]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1241, hc01, hc12, hlam, hphi, p1603_1]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        rcases p1603_3 (m.d 0 1) (by simp) with h1620 | h1620
                        · linarith only [h1620, hlam, p1603_0]
                        · rcases p1603_3 (m.d 1 2) (by simp) with h1622 | h1622
                          · rcases p1603_3 (m.d 1 3) (by simp) with h1623 | h1623
                            · rcases p1603_3 (m.d 1 4) (by simp) with h1624 | h1624
                              · linarith only [h1495, h1624, hlam]
                              · linarith only [h1497, h1501, h1624, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1603_1]
                            · linarith only [h1623, hlam, p1603_0]
                          · linarith only [h0, h1622, hlam]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1492, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1492, h1497, h1501, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1603_1]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1241, h1492, hc01, hc12, hlam, hphi, p1603_1]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        rcases p1603_3 (m.d 0 1) (by simp) with h1633 | h1633
                        · linarith only [h1633, hlam, p1603_0]
                        · rcases p1603_3 (m.d 1 2) (by simp) with h1635 | h1635
                          · rcases p1603_3 (m.d 1 3) (by simp) with h1636 | h1636
                            · rcases p1603_3 (m.d 1 4) (by simp) with h1637 | h1637
                              · rcases p1603_3 (m.d 1 5) (by simp) with h1638 | h1638
                                · linarith only [h1497, h1638, hlam]
                                · linarith only [h1241, h1638, hlam]
                              · linarith only [h1637, hlam, p1603_0]
                            · linarith only [h1636, h927, hlam]
                          · linarith only [h0, h1635, hlam]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1493, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1495, hlam, p1603_1]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1241, hc01, hc14, hlam, hphi, p1603_1]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        rcases p1603_3 (m.d 0 1) (by simp) with h1648 | h1648
                        · linarith only [h1648, hlam, p1603_0]
                        · rcases p1603_3 (m.d 1 2) (by simp) with h1650 | h1650
                          · rcases p1603_3 (m.d 1 3) (by simp) with h1651 | h1651
                            · rcases p1603_3 (m.d 1 4) (by simp) with h1652 | h1652
                              · rcases p1603_3 (m.d 1 5) (by simp) with h1653 | h1653
                                · rcases h5bigk with h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [hlam, p1654_0]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1241, hlam, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1654_1, u2ehi4]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    rcases p1654_3 (m.d 0 5) (by simp) with h1658 | h1658
                                    · rcases p1654_3 (m.d 1 5) (by simp) with h1659 | h1659
                                      · rcases p1654_3 (m.d 2 5) (by simp) with h1660 | h1660
                                        · linarith only [h1488, h1660, hlam]
                                        · linarith only [h1499, h1660, hlam]
                                      · linarith only [h1496, h1659, hlam]
                                    · linarith only [h1490, h1658, hlam]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1489, h1491, h1501, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1241, h1492, h1495, h1497, hc01, hc12, hlam, hphi, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [hlam, p1654_0]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1492, h1495, h1497, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1654_1, u2ehi4]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    rcases p1654_3 (m.d 0 5) (by simp) with h1669 | h1669
                                    · linarith only [h1241, h1669, hlam]
                                    · linarith only [h1490, h1669, hlam]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1492, h1495, h1497, h1501, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1488, hlam, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1494, hlam, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [hlam, p1654_0]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h0, h1488, h1501, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h0, h1486, h1498, h1500, h1501, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1490, hlam, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1496, hlam, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1499, hlam, p1654_0]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [hlam, p1654_0]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1501, hlam, p1654_0]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1491, hlam, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1497, hlam, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1500, hlam, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [h1501, hc34, hc45, hlam, hphi, p1654_1]
                                  · have p1654_0 := h1654c.1
                                    have p1654_1 := h1654c.2.1
                                    have p1654_2 := h1654c.2.2.1
                                    have p1654_3 := h1654c.2.2.2
                                    linarith only [hlam, p1654_0]
                                · linarith only [h1653, hlam, p1603_0]
                              · linarith only [h1497, h1652, hlam, p1603_1]
                            · linarith only [h1651, h927, hlam]
                          · linarith only [h0, h1650, hlam]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1494, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1496, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [h1497, hlam, p1603_0]
                      · have p1603_0 := h1603c.1
                        have p1603_1 := h1603c.2.1
                        have p1603_2 := h1603c.2.2.1
                        have p1603_3 := h1603c.2.2.2
                        linarith only [hlam, p1603_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1696 | h1696
                    · linarith only [h1500, h1696, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h1bigk with h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h0, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h927, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1241, h1497, hlam, p1698_1]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1241, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        rcases p1698_3 (m.d 0 1) (by simp) with h1704 | h1704
                        · linarith only [h1704, hlam, p1698_0]
                        · rcases p1698_3 (m.d 1 2) (by simp) with h1706 | h1706
                          · rcases p1698_3 (m.d 1 3) (by simp) with h1707 | h1707
                            · linarith only [h1492, h1707, hlam]
                            · linarith only [h1707, h927, hlam]
                          · linarith only [h1706, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1489, h1491, h1500, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi3]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1241, h1497, hc01, hc12, hlam, hphi, p1698_1]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1241, h1491, h1500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi3]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        rcases p1698_3 (m.d 0 1) (by simp) with h1715 | h1715
                        · linarith only [h1715, hlam, p1698_0]
                        · rcases p1698_3 (m.d 1 2) (by simp) with h1717 | h1717
                          · rcases p1698_3 (m.d 1 3) (by simp) with h1718 | h1718
                            · rcases p1698_3 (m.d 1 4) (by simp) with h1719 | h1719
                              · linarith only [h1495, h1719, hlam]
                              · linarith only [h0, h1497, h1500, h1719, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1718, hlam, p1698_0]
                          · linarith only [h0, h1717, hlam]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1492, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1497, h1500, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi3]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1241, h1491, h1492, h1500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi3]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        rcases p1698_3 (m.d 0 1) (by simp) with h1728 | h1728
                        · linarith only [h1728, hlam, p1698_0]
                        · rcases p1698_3 (m.d 1 2) (by simp) with h1730 | h1730
                          · rcases p1698_3 (m.d 1 3) (by simp) with h1731 | h1731
                            · rcases p1698_3 (m.d 1 4) (by simp) with h1732 | h1732
                              · rcases p1698_3 (m.d 1 5) (by simp) with h1733 | h1733
                                · linarith only [h1497, h1733, hlam]
                                · linarith only [h1241, h1733, hlam]
                              · linarith only [h1732, hlam, p1698_0]
                            · linarith only [h1731, h927, hlam]
                          · linarith only [h0, h1730, hlam]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1493, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1495, hlam, p1698_1]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1241, h1491, h1500, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi3]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        rcases p1698_3 (m.d 0 1) (by simp) with h1743 | h1743
                        · linarith only [h1743, hlam, p1698_0]
                        · rcases p1698_3 (m.d 1 2) (by simp) with h1745 | h1745
                          · rcases p1698_3 (m.d 1 3) (by simp) with h1746 | h1746
                            · rcases p1698_3 (m.d 1 4) (by simp) with h1747 | h1747
                              · rcases p1698_3 (m.d 1 5) (by simp) with h1748 | h1748
                                · rcases h5bigk with h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [hlam, p1749_0]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1241, hlam, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1749_1, u2ehi4]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    rcases p1749_3 (m.d 0 5) (by simp) with h1753 | h1753
                                    · rcases p1749_3 (m.d 1 5) (by simp) with h1754 | h1754
                                      · rcases p1749_3 (m.d 2 5) (by simp) with h1755 | h1755
                                        · linarith only [h1488, h1755, hlam]
                                        · linarith only [h1499, h1755, hlam]
                                      · linarith only [h1496, h1754, hlam]
                                    · linarith only [h1490, h1753, hlam]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1500, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1749_1, u2ehi3]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1241, hc01, hc15, hlam, hphi, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [hlam, p1749_0]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1494, h1500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1749_1, u2ehi3]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    rcases p1749_3 (m.d 0 5) (by simp) with h1764 | h1764
                                    · linarith only [h1241, h1764, hlam]
                                    · linarith only [h1490, h1764, hlam]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1492, h1495, h1497, h1500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1749_1, u2ehi3]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1488, hlam, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1494, hlam, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [hlam, p1749_0]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h0, h1488, h1696, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1500, hlam, p1749_0]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1490, hlam, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1496, hlam, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1499, hlam, p1749_0]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [hlam, p1749_0]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1696, hlam, p1749_0]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1491, hlam, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1497, hlam, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1489, h1491, hc03, hc25, hlam, hphi, ht0b, ht5b, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [h1489, h1491, h1492, h1696, h927, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1749_1]
                                  · have p1749_0 := h1749c.1
                                    have p1749_1 := h1749c.2.1
                                    have p1749_2 := h1749c.2.2.1
                                    have p1749_3 := h1749c.2.2.2
                                    linarith only [hlam, p1749_0]
                                · linarith only [h1748, hlam, p1698_0]
                              · linarith only [h1497, h1747, hlam, p1698_1]
                            · linarith only [h1746, h927, hlam]
                          · linarith only [h0, h1745, hlam]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1494, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1496, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [h1497, hlam, p1698_0]
                      · have p1698_0 := h1698c.1
                        have p1698_1 := h1698c.2.1
                        have p1698_2 := h1698c.2.2.1
                        have p1698_3 := h1698c.2.2.2
                        linarith only [hlam, p1698_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1791 | h1791
                  · linarith only [h1498, h1499, h1791, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1793 | h1793
                    · linarith only [h1791, h1793, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h1bigk with h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h0, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h927, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1497, h1498, h1499, h1793, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1795_1, u2ehi3]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1241, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        rcases p1795_3 (m.d 0 1) (by simp) with h1801 | h1801
                        · linarith only [h1801, hlam, p1795_0]
                        · rcases p1795_3 (m.d 1 2) (by simp) with h1803 | h1803
                          · rcases p1795_3 (m.d 1 3) (by simp) with h1804 | h1804
                            · linarith only [h1492, h1804, hlam]
                            · linarith only [h1804, h927, hlam]
                          · linarith only [h1803, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h927, hc01, hc12, hlam, hphi, p1795_1]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1241, h1491, h1497, h1498, h1499, h1793, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1795_1, u2ehi3]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1241, h1491, h1498, h1499, h1793, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1795_1, u2ehi3]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        rcases p1795_3 (m.d 0 1) (by simp) with h1812 | h1812
                        · linarith only [h1812, hlam, p1795_0]
                        · rcases p1795_3 (m.d 1 2) (by simp) with h1814 | h1814
                          · rcases p1795_3 (m.d 1 3) (by simp) with h1815 | h1815
                            · rcases p1795_3 (m.d 1 4) (by simp) with h1816 | h1816
                              · linarith only [h1495, h1816, hlam]
                              · linarith only [h0, h1497, h1498, h1499, h1793, h1816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1815, hlam, p1795_0]
                          · linarith only [h0, h1814, hlam]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1492, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1497, h1498, h1499, h1793, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1795_1, u2ehi3]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1241, h1491, h1492, h1498, h1499, h1793, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1795_1, u2ehi3]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        rcases p1795_3 (m.d 0 1) (by simp) with h1825 | h1825
                        · linarith only [h1825, hlam, p1795_0]
                        · rcases p1795_3 (m.d 1 2) (by simp) with h1827 | h1827
                          · rcases p1795_3 (m.d 1 3) (by simp) with h1828 | h1828
                            · rcases p1795_3 (m.d 1 4) (by simp) with h1829 | h1829
                              · rcases p1795_3 (m.d 1 5) (by simp) with h1830 | h1830
                                · linarith only [h1497, h1830, hlam]
                                · linarith only [h1241, h1830, hlam]
                              · linarith only [h1829, hlam, p1795_0]
                            · linarith only [h1828, h927, hlam]
                          · linarith only [h0, h1827, hlam]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1493, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1495, hlam, p1795_1]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1241, h1491, h1498, h1499, h1793, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1795_1, u2ehi3]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        rcases p1795_3 (m.d 0 1) (by simp) with h1840 | h1840
                        · linarith only [h1840, hlam, p1795_0]
                        · rcases p1795_3 (m.d 1 2) (by simp) with h1842 | h1842
                          · rcases p1795_3 (m.d 1 3) (by simp) with h1843 | h1843
                            · rcases p1795_3 (m.d 1 4) (by simp) with h1844 | h1844
                              · rcases p1795_3 (m.d 1 5) (by simp) with h1845 | h1845
                                · rcases h5bigk with h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c | h1846c
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [hlam, p1846_0]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1241, hlam, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1498, h1499, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1846_1, u2ehi3]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1498, h1499, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1846_1, u2ehi3]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1489, h1491, h1492, h1498, h1499, h1793, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1846_1, u2ehi3]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1241, hc01, hc15, hlam, hphi, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [hlam, p1846_0]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1494, h1498, h1499, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1846_1, u2ehi3]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1492, h1496, h1498, h1499, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1846_1, u2ehi3]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1492, h1495, h1497, h1498, h1499, h1793, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1846_1, u2ehi3]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1488, hlam, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1494, hlam, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [hlam, p1846_0]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1499, hlam, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1791, hlam, p1846_0]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1490, hlam, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1496, hlam, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1491, h1498, h1499, h1793, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1846_1, u2ehi3]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [hlam, p1846_0]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1793, hlam, p1846_0]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1491, hlam, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1497, hlam, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1489, h1491, h1492, h1498, h1499, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1846_1, u2ehi3]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [h1489, h1491, h1492, h927, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1846_1]
                                  · have p1846_0 := h1846c.1
                                    have p1846_1 := h1846c.2.1
                                    have p1846_2 := h1846c.2.2.1
                                    have p1846_3 := h1846c.2.2.2
                                    linarith only [hlam, p1846_0]
                                · linarith only [h1845, hlam, p1795_0]
                              · linarith only [h1497, h1844, hlam, p1795_1]
                            · linarith only [h1843, h927, hlam]
                          · linarith only [h0, h1842, hlam]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1494, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1496, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [h1497, hlam, p1795_0]
                      · have p1795_0 := h1795c.1
                        have p1795_1 := h1795c.2.1
                        have p1795_2 := h1795c.2.2.1
                        have p1795_3 := h1795c.2.2.2
                        linarith only [hlam, p1795_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1880 | h1880
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1881 | h1881
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1882 | h1882
                    · rcases h1bigk with h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h0, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h927, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1241, h1495, h1498, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1883_1]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1241, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        rcases p1883_3 (m.d 0 1) (by simp) with h1889 | h1889
                        · linarith only [h1889, hlam, p1883_0]
                        · rcases p1883_3 (m.d 1 2) (by simp) with h1891 | h1891
                          · rcases p1883_3 (m.d 1 3) (by simp) with h1892 | h1892
                            · linarith only [h1492, h1892, hlam]
                            · linarith only [h1892, h927, hlam]
                          · linarith only [h1891, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h927, hc01, hc12, hlam, hphi, p1883_1]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1241, h1497, hc01, hc12, hlam, hphi, p1883_1]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1241, hc01, hc12, hlam, hphi, p1883_1]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        rcases p1883_3 (m.d 0 1) (by simp) with h1900 | h1900
                        · linarith only [h1900, hlam, p1883_0]
                        · rcases p1883_3 (m.d 1 2) (by simp) with h1902 | h1902
                          · rcases p1883_3 (m.d 1 3) (by simp) with h1903 | h1903
                            · rcases p1883_3 (m.d 1 4) (by simp) with h1904 | h1904
                              · linarith only [h1495, h1904, hlam]
                              · linarith only [h1495, h1498, h1880, h1904, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1883_1, u2ehi4]
                            · linarith only [h1903, hlam, p1883_0]
                          · linarith only [h0, h1902, hlam]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1492, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1492, h1495, h1498, h1880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1883_1, u2ehi4]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1241, h1492, hc01, hc12, hlam, hphi, p1883_1]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        rcases p1883_3 (m.d 0 1) (by simp) with h1913 | h1913
                        · linarith only [h1913, hlam, p1883_0]
                        · rcases p1883_3 (m.d 1 2) (by simp) with h1915 | h1915
                          · rcases p1883_3 (m.d 1 3) (by simp) with h1916 | h1916
                            · rcases p1883_3 (m.d 1 4) (by simp) with h1917 | h1917
                              · rcases p1883_3 (m.d 1 5) (by simp) with h1918 | h1918
                                · linarith only [h1497, h1918, hlam]
                                · linarith only [h1241, h1918, hlam]
                              · linarith only [h1917, hlam, p1883_0]
                            · linarith only [h1916, h927, hlam]
                          · linarith only [h0, h1915, hlam]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1493, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1495, hlam, p1883_1]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1241, hc01, hc14, hlam, hphi, p1883_1]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        rcases p1883_3 (m.d 0 1) (by simp) with h1928 | h1928
                        · linarith only [h1928, hlam, p1883_0]
                        · rcases p1883_3 (m.d 1 2) (by simp) with h1930 | h1930
                          · rcases p1883_3 (m.d 1 3) (by simp) with h1931 | h1931
                            · rcases p1883_3 (m.d 1 4) (by simp) with h1932 | h1932
                              · rcases p1883_3 (m.d 1 5) (by simp) with h1933 | h1933
                                · rcases h5bigk with h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [hlam, p1934_0]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1241, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1934_1, u2ehi4]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    rcases p1934_3 (m.d 0 5) (by simp) with h1938 | h1938
                                    · rcases p1934_3 (m.d 1 5) (by simp) with h1939 | h1939
                                      · rcases p1934_3 (m.d 2 5) (by simp) with h1940 | h1940
                                        · linarith only [h1488, h1940, hlam]
                                        · linarith only [h1880, h1940, hlam]
                                      · linarith only [h1496, h1939, hlam]
                                    · linarith only [h1490, h1938, hlam]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    rcases p1934_3 (m.d 0 5) (by simp) with h1945 | h1945
                                    · rcases p1934_3 (m.d 1 5) (by simp) with h1946 | h1946
                                      · rcases p1934_3 (m.d 2 5) (by simp) with h1947 | h1947
                                        · linarith only [h1488, h1947, hlam]
                                        · linarith only [h1881, h1947, hlam]
                                      · linarith only [h1497, h1946, hlam]
                                    · linarith only [h1491, h1945, hlam]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1241, h1492, h1495, h1497, hc01, hc12, hlam, hphi, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [hlam, p1934_0]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1492, h1495, h1497, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1934_1, u2ehi4]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    rcases p1934_3 (m.d 0 5) (by simp) with h1955 | h1955
                                    · linarith only [h1241, h1955, hlam]
                                    · linarith only [h1490, h1955, hlam]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    rcases p1934_3 (m.d 0 5) (by simp) with h1958 | h1958
                                    · linarith only [h1241, h1958, hlam]
                                    · linarith only [h1491, h1958, hlam]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1488, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1494, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [hlam, p1934_0]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1489, h1498, h1880, h1882, hc03, hc45, hlam, hphi, ht0b, ht5b, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1489, h1492, h1498, h1880, h927, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1490, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1496, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1880, hlam, p1934_0]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [hlam, p1934_0]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1490, h1492, h927, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1491, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1497, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1881, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [h1882, hlam, p1934_1]
                                  · have p1934_0 := h1934c.1
                                    have p1934_1 := h1934c.2.1
                                    have p1934_2 := h1934c.2.2.1
                                    have p1934_3 := h1934c.2.2.2
                                    linarith only [hlam, p1934_0]
                                · linarith only [h1933, hlam, p1883_0]
                              · linarith only [h1497, h1932, hlam, p1883_1]
                            · linarith only [h1931, h927, hlam]
                          · linarith only [h0, h1930, hlam]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1494, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1496, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [h1497, hlam, p1883_0]
                      · have p1883_0 := h1883c.1
                        have p1883_1 := h1883c.2.1
                        have p1883_2 := h1883c.2.2.1
                        have p1883_3 := h1883c.2.2.2
                        linarith only [hlam, p1883_0]
                    · linarith only [h1498, h1880, h1882, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · linarith only [h1498, h1880, h1881, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1986 | h1986
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1987 | h1987
                    · rcases h1bigk with h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c | h1988c
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h0, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h927, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1241, h1497, hlam, p1988_1]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1241, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        rcases p1988_3 (m.d 0 1) (by simp) with h1994 | h1994
                        · linarith only [h1994, hlam, p1988_0]
                        · rcases p1988_3 (m.d 1 2) (by simp) with h1996 | h1996
                          · rcases p1988_3 (m.d 1 3) (by simp) with h1997 | h1997
                            · linarith only [h1492, h1997, hlam]
                            · linarith only [h1997, h927, hlam]
                          · linarith only [h1996, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h927, hc01, hc12, hlam, hphi, p1988_1]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1241, h1490, h1497, h1880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1988_1, u2ehi2]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1241, h1490, h1880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1988_1, u2ehi2]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        rcases p1988_3 (m.d 0 1) (by simp) with h2005 | h2005
                        · linarith only [h2005, hlam, p1988_0]
                        · rcases p1988_3 (m.d 1 2) (by simp) with h2007 | h2007
                          · rcases p1988_3 (m.d 1 3) (by simp) with h2008 | h2008
                            · rcases p1988_3 (m.d 1 4) (by simp) with h2009 | h2009
                              · linarith only [h1495, h2009, hlam]
                              · linarith only [h1241, h1490, h1497, h1880, h2009, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1988_1, u2ehi2]
                            · linarith only [h2008, hlam, p1988_0]
                          · linarith only [h0, h2007, hlam]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1492, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1241, h1490, h1492, h1497, h1880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1988_1, u2ehi2]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1241, h1490, h1492, h1880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1988_1, u2ehi2]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        rcases p1988_3 (m.d 0 1) (by simp) with h2018 | h2018
                        · linarith only [h2018, hlam, p1988_0]
                        · rcases p1988_3 (m.d 1 2) (by simp) with h2020 | h2020
                          · rcases p1988_3 (m.d 1 3) (by simp) with h2021 | h2021
                            · rcases p1988_3 (m.d 1 4) (by simp) with h2022 | h2022
                              · rcases p1988_3 (m.d 1 5) (by simp) with h2023 | h2023
                                · linarith only [h1497, h2023, hlam]
                                · linarith only [h1241, h2023, hlam]
                              · linarith only [h2022, hlam, p1988_0]
                            · linarith only [h2021, h927, hlam]
                          · linarith only [h0, h2020, hlam]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1493, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1495, hlam, p1988_1]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1241, h1490, h1880, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1988_1, u2ehi2]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        rcases p1988_3 (m.d 0 1) (by simp) with h2033 | h2033
                        · linarith only [h2033, hlam, p1988_0]
                        · rcases p1988_3 (m.d 1 2) (by simp) with h2035 | h2035
                          · rcases p1988_3 (m.d 1 3) (by simp) with h2036 | h2036
                            · rcases p1988_3 (m.d 1 4) (by simp) with h2037 | h2037
                              · rcases p1988_3 (m.d 1 5) (by simp) with h2038 | h2038
                                · rcases h5bigk with h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [hlam, p2039_0]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1241, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1880, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2039_1, u2ehi2]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1880, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2039_1, u2ehi2]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    rcases p2039_3 (m.d 0 5) (by simp) with h2044 | h2044
                                    · rcases p2039_3 (m.d 1 5) (by simp) with h2045 | h2045
                                      · rcases p2039_3 (m.d 2 5) (by simp) with h2046 | h2046
                                        · linarith only [h1488, h2046, hlam]
                                        · linarith only [h1986, h2046, hlam]
                                      · linarith only [h1497, h2045, hlam]
                                    · linarith only [h1491, h2044, hlam]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1241, h1492, h1495, h1497, hc01, hc12, hlam, hphi, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [hlam, p2039_0]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1492, h1495, h1497, h1880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2039_1, u2ehi2]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1492, h1495, h1497, h1880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2039_1, u2ehi2]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    rcases p2039_3 (m.d 0 5) (by simp) with h2055 | h2055
                                    · linarith only [h1241, h2055, hlam]
                                    · linarith only [h1491, h2055, hlam]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1488, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1494, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [hlam, p2039_0]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1880, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h0, h1487, h1986, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1490, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1496, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht23, p2039_1, u2ehi4]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [hlam, p2039_0]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1489, h1492, h1987, h927, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1491, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1497, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1986, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [h1987, hlam, p2039_1]
                                  · have p2039_0 := h2039c.1
                                    have p2039_1 := h2039c.2.1
                                    have p2039_2 := h2039c.2.2.1
                                    have p2039_3 := h2039c.2.2.2
                                    linarith only [hlam, p2039_0]
                                · linarith only [h2038, hlam, p1988_0]
                              · linarith only [h1497, h2037, hlam, p1988_1]
                            · linarith only [h2036, h927, hlam]
                          · linarith only [h0, h2035, hlam]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1494, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1496, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [h1497, hlam, p1988_0]
                      · have p1988_0 := h1988c.1
                        have p1988_1 := h1988c.2.1
                        have p1988_2 := h1988c.2.2.1
                        have p1988_3 := h1988c.2.2.2
                        linarith only [hlam, p1988_0]
                    · linarith only [h1498, h1987, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2082 | h2082
                    · linarith only [h1498, h1986, h2082, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h1489, h1491, h1492, h1498, h2082, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h1241, h1491, h1497, hlam]
          · linarith only [h1490, h1496, h927, hlam]
        · linarith only [h0, h1486, h1489, h1495, h927, hc01, hc12, hlam, hphi]
      · linarith only [h0, h1486, h1494, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1486, h1493, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h1486, h1492, hlam]

end R2N4
