import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1452 | h1452
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1453 | h1453
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1454 | h1454
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1455 | h1455
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1456 | h1456
          · linarith only [h1452, h1456, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1458 | h1458
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1459 | h1459
              · linarith only [h1455, h1456, h1459, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1461 | h1461
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1462 | h1462
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1463 | h1463
                    · linarith only [h1459, h1463, h4, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1465 | h1465
                      · linarith only [h1463, h1465, h4, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · linarith only [h1, h1461, h1463, h1465, h4, h5, hc23, hc34, hlam, hphi]
                  · linarith only [h1453, h1454, h1455, h1456, h1461, h1462, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1469 | h1469
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1470 | h1470
                    · linarith only [h1470, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h1453, h1461, h1470, h4, h5, hc13, hc34, hlam, hphi]
                  · linarith only [h1454, h1456, h1458, h1469, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h1452, h1458, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1455, h4, h5, hc12, hc24, hlam, hphi]
      · linarith only [h1453, h1454, h4, h5, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1477 | h1477
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1478 | h1478
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1479 | h1479
          · linarith only [h0, h1479, h5, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1481 | h1481
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1482 | h1482
              · linarith only [h1478, h1479, h1482, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1484 | h1484
                · linarith only [h1, h1453, h1484, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1486 | h1486
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1487 | h1487
                    · linarith only [h1482, h1487, h4, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1489 | h1489
                      · linarith only [h1, h1453, h1478, h1489, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1491 | h1491
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1492 | h1492
                          · rcases h1bigk with h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1481, h1491, hc01, hlam, hphi, ht0b, ht45, ht5b, p1493_1, u4ehi4]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              rcases p1493_3 (m.d 0 1) (by simp) with h1496 | h1496
                              · rcases p1493_3 (m.d 1 2) (by simp) with h1497 | h1497
                                · linarith only [h0, h1497, hlam]
                                · linarith only [h1478, h1497, hlam]
                              · linarith only [h1496, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1479, h1481, h1491, hc01, hlam, hphi, ht0b, ht45, ht5b, p1493_1, u4ehi4]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              rcases p1493_3 (m.d 0 1) (by simp) with h1502 | h1502
                              · rcases p1493_3 (m.d 1 2) (by simp) with h1503 | h1503
                                · linarith only [h0, h1503, hlam]
                                · linarith only [h1481, h1503, hlam]
                              · linarith only [h1502, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h0, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h0, h1478, h1487, h5, hc23, hc34, hlam, hphi, p1493_1]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1479, hlam, p1493_1]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h0, h1481, h1487, h1491, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1493_1, u4ehi4]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1478, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1482, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1484, hlam, p1493_1]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h2, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1478, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1493_1]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              rcases p1493_3 (m.d 0 1) (by simp) with h1519 | h1519
                              · rcases p1493_3 (m.d 1 2) (by simp) with h1520 | h1520
                                · linarith only [h1479, h1520, hlam]
                                · linarith only [h1478, h1520, hlam]
                              · linarith only [h1, h1519, hlam]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1481, h1491, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1493_1, u4ehi4]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h3, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1481, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1452, h1478, h1487, h3, h5, hc23, hc34, hlam, hphi, p1493_1]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [h1486, hlam, p1493_0]
                            · have p1493_0 := h1493c.1
                              have p1493_1 := h1493c.2.1
                              have p1493_2 := h1493c.2.2.1
                              have p1493_3 := h1493c.2.2.2
                              linarith only [hlam, p1493_0]
                          · linarith only [h0, h1481, h1487, h1491, h1492, h5, hlam]
                        · linarith only [h0, h1481, h1491, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                  · linarith only [h1452, h1477, h1479, h1481, h1486, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · linarith only [h1452, h1481, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1478, h4, h5, hc12, hc24, hlam, hphi]
      · linarith only [h1452, h1477, h5, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1537 | h1537
    · linarith only [h1452, h1537, h4, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1539 | h1539
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1541 | h1541
          · linarith only [h0, h1541, h5, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1543 | h1543
            · linarith only [h0, h1452, h1543, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1545 | h1545
              · linarith only [h1540, h1541, h1545, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1547 | h1547
                · linarith only [h1537, h1545, h1547, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1549 | h1549
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1550 | h1550
                    · linarith only [h1550, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1552 | h1552
                      · linarith only [h0, h1, h1537, h1540, h1552, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1554 | h1554
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1555 | h1555
                          · rcases h1bigk with h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              rcases p1556_3 (m.d 0 1) (by simp) with h1558 | h1558
                              · rcases p1556_3 (m.d 1 2) (by simp) with h1559 | h1559
                                · linarith only [h1559, hlam, p1556_0]
                                · rcases p1556_3 (m.d 1 3) (by simp) with h1561 | h1561
                                  · linarith only [h1, h1561, hlam]
                                  · rcases p1556_3 (m.d 1 4) (by simp) with h1563 | h1563
                                    · linarith only [h1563, h2, hlam]
                                    · linarith only [h1541, h1563, hlam]
                              · linarith only [h1558, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              rcases p1556_3 (m.d 0 1) (by simp) with h1567 | h1567
                              · rcases p1556_3 (m.d 1 2) (by simp) with h1568 | h1568
                                · linarith only [h0, h1568, hlam]
                                · linarith only [h1540, h1568, hlam]
                              · linarith only [h1567, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1549, hc01, hlam, hphi, ht0b, ht45, ht5b, p1556_1, u4ehi4]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              rcases p1556_3 (m.d 0 1) (by simp) with h1573 | h1573
                              · rcases p1556_3 (m.d 1 2) (by simp) with h1574 | h1574
                                · linarith only [h0, h1574, hlam]
                                · rcases p1556_3 (m.d 1 3) (by simp) with h1576 | h1576
                                  · linarith only [h1, h1576, hlam]
                                  · rcases p1556_3 (m.d 1 4) (by simp) with h1578 | h1578
                                    · linarith only [h1578, h2, hlam]
                                    · linarith only [h1549, h1578, hlam]
                              · linarith only [h1573, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h0, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h0, h1452, h1540, h1550, h1554, hc23, hc34, hlam, hphi, p1556_1]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1541, hlam, p1556_1]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1543, hlam, p1556_1]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1540, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1545, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1547, hlam, p1556_1]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h2, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1540, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1556_1]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              rcases p1556_3 (m.d 0 1) (by simp) with h1594 | h1594
                              · rcases p1556_3 (m.d 1 2) (by simp) with h1595 | h1595
                                · linarith only [h1541, h1595, hlam]
                                · linarith only [h1540, h1595, hlam]
                              · linarith only [h1, h1594, hlam]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1540, h1543, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1556_1]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h3, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1540, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1556_1]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              rcases p1556_3 (m.d 0 1) (by simp) with h1603 | h1603
                              · rcases p1556_3 (m.d 1 2) (by simp) with h1604 | h1604
                                · linarith only [h1543, h1604, hlam]
                                · linarith only [h1540, h1604, hlam]
                              · linarith only [h1, h1603, hlam]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [h1549, hlam, p1556_0]
                            · have p1556_0 := h1556c.1
                              have p1556_1 := h1556c.2.1
                              have p1556_2 := h1556c.2.2.1
                              have p1556_3 := h1556c.2.2.2
                              linarith only [hlam, p1556_0]
                          · linarith only [h0, h1452, h1540, h1550, h1554, h1555, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h1549, h1554, h2, h5, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1612 | h1612
                    · linarith only [h1539, h1540, h1541, h1549, h1612, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h1539, h1540, h1541, h1549, h1612, h5, hc23, hc34, hlam, hphi]
        · linarith only [h1540, h4, h5, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1616 | h1616
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1617 | h1617
          · linarith only [h0, h1539, h1617, h5, hc45, hlam, hphi, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1619 | h1619
            · linarith only [h0, h1452, h1619, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1621 | h1621
              · linarith only [h1, h1539, h1621, h4, h5, hc45, hlam, hphi, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1623 | h1623
                · linarith only [h1537, h1621, h1623, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1625 | h1625
                  · linarith only [h1539, h1625, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1627 | h1627
                    · linarith only [h0, h1616, h1627, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1629 | h1629
                      · linarith only [h0, h1537, h1539, h1616, h1629, h5, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1631 | h1631
                        · linarith only [h0, h1539, h1616, h1627, h1631, h5, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h1616, h1631, h5, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h1616, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1635 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1636 | h1636
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1637 | h1637
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1638 | h1638
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1639 | h1639
        · linarith only [h1635, h1639, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1641 | h1641
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1642 | h1642
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1643 | h1643
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1644 | h1644
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1645 | h1645
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1646 | h1646
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1647 | h1647
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1648 | h1648
                        · linarith only [h1635, h1648, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h1, h1639, h1641, h1645, h1648, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h1642, h1647, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h1635, h1645, h1646, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h1635, h1638, h1645, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h1635, h1637, h1638, h1639, h1641, h1644, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h1639, h1641, h1643, hlam]
            · linarith only [h1636, h1641, h1642, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
          · linarith only [h1635, h1641, h4, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1658 | h1658
        · linarith only [h1635, h1658, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1660 | h1660
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1661 | h1661
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1662 | h1662
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1663 | h1663
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1664 | h1664
                  · linarith only [h1638, h1664, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1666 | h1666
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1667 | h1667
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1668 | h1668
                        · linarith only [h1638, h1660, h1668, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1670 | h1670
                          · linarith only [h0, h1638, h1661, h1666, h1668, h1670, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases h1bigk with h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c | h1672c
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1661, h1666, h1668, hc01, hlam, hphi, ht0b, ht45, ht5b, p1672_1, u4ehi3]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1658, h1661, h1666, h1668, hc01, hlam, hphi, ht0b, ht45, ht5b, p1672_1, u4ehi3]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              rcases p1672_3 (m.d 0 1) (by simp) with h1676 | h1676
                              · rcases p1672_3 (m.d 1 2) (by simp) with h1677 | h1677
                                · linarith only [h0, h1677, hlam]
                                · linarith only [h1660, h1677, hlam]
                              · linarith only [h1676, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              rcases p1672_3 (m.d 0 1) (by simp) with h1681 | h1681
                              · rcases p1672_3 (m.d 1 2) (by simp) with h1682 | h1682
                                · linarith only [h0, h1682, hlam]
                                · linarith only [h1661, h1682, hlam]
                              · linarith only [h1681, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h0, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1658, hlam, p1672_1]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h0, h1660, h1666, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1672_1, u4ehi3]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h0, h1660, h1664, h1666, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1672_1, u4ehi3]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1, h1660, h1666, hc01, hlam, hphi, ht0b, ht45, ht5b, p1672_1, u4ehi3]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1, h1660, h1666, hc01, hlam, hphi, ht0b, ht45, ht5b, p1672_1, u4ehi3]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1, h1660, h1664, h1666, hc01, hlam, hphi, ht0b, ht45, ht5b, p1672_1, u4ehi3]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h2, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1660, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1662, hlam, p1672_1]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1664, hlam, p1672_1]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h3, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1661, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1663, hlam, p1672_0]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [h1660, h1666, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1672_1, u4ehi3]
                            · have p1672_0 := h1672c.1
                              have p1672_1 := h1672c.2.1
                              have p1672_2 := h1672c.2.2.1
                              have p1672_3 := h1672c.2.2.2
                              linarith only [hlam, p1672_0]
                      · linarith only [h0, h1661, h1667, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h1660, h1666, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h1637, h1662, h1663, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h1638, h1658, h1660, h1662, h2, hc45, hlam, hphi, u4ehi2]
            · linarith only [h1636, h1660, h1661, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · linarith only [h1635, h1660, h4, hc12, hc23, hlam, hphi]
    · linarith only [h1636, h1637, h4, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1713 | h1713
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1714 | h1714
      · linarith only [h1635, h1636, h1714, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1716 | h1716
        · linarith only [h0, h1716, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1718 | h1718
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1719 | h1719
            · linarith only [h0, h1636, h1719, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1721 | h1721
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1722 | h1722
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1723 | h1723
                  · linarith only [h1714, h1723, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1725 | h1725
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1726 | h1726
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1727 | h1727
                        · linarith only [h0, h1636, h1714, h1718, h1726, h1727, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                        · linarith only [h1635, h1636, h1725, h1727, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h0, h1718, h1722, h1725, h1726, h4, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h1718, h1725, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h1713, h1716, h1718, h1722, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h1714, h1716, h1718, h1721, h2, hc45, hlam, hphi, u4ehi2]
          · linarith only [h1635, h1636, h1718, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1735 | h1735
      · linarith only [h1635, h1713, h1735, h4, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1737 | h1737
        · linarith only [h1635, h1737, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1739 | h1739
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1740 | h1740
            · linarith only [h0, h1636, h1740, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1742 | h1742
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1743 | h1743
                · linarith only [h1, h1713, h1743, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1745 | h1745
                  · linarith only [h1735, h1745, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1747 | h1747
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1748 | h1748
                      · linarith only [h0, h1713, h1739, h1747, h1748, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h1739, h1747, h1748, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h1739, h1747, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h1735, h1737, h1739, h1742, h2, hc45, hlam, hphi, u4ehi2]
          · linarith only [h1635, h1713, h1739, h4, hc12, hc35, hlam, hphi, ht23]

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1635 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1754 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h1755 | h1755
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1756 | h1756
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1757 | h1757
      · linarith only [h0, h1757, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1759 | h1759
        · linarith only [h1635, h1754, h1759, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1761 | h1761
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1762 | h1762
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1763 | h1763
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1764 | h1764
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1765 | h1765
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1766 | h1766
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1767 | h1767
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1768 | h1768
                        · linarith only [h1, h1762, h1768, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h1635, h1761, h1765, h1767, h1768, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h1635, h1761, h1767, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h0, h1635, h1761, h1765, h1766, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h1761, h1765, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h1754, h1756, h1759, h1761, h1764, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h1755, h1759, h1761, h1762, h1763, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1776 | h1776
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1777 | h1777
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1778 | h1778
                  · linarith only [h1762, h1776, h1778, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h1761, h1778, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h1635, h1756, h1757, h1761, h1762, h1777, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h1755, h1757, h1761, h1776, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
          · linarith only [h1754, h1761, h4, hc12, hc23, hlam, hphi]
    · linarith only [h1635, h1754, h1756, hlam]
  · linarith only [h1754, h1755, h4, hlam]

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1635 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1754 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1786 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h1787 | h1787
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1788 | h1788
    · linarith only [h0, h1788, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1790 | h1790
      · linarith only [h0, h1635, h1790, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1792 | h1792
        · linarith only [h0, h1754, h1792, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1794 | h1794
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1795 | h1795
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1796 | h1796
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1797 | h1797
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1798 | h1798
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1799 | h1799
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1800 | h1800
                      · linarith only [h1, h1794, h1800, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h1796, h1800, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h1, h1635, h1794, h1796, h1799, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h1786, h1798, h4, hlam]
                · linarith only [h1, h1794, h1797, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1806 | h1806
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1807 | h1807
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1808 | h1808
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1809 | h1809
                      · linarith only [h1794, h1796, h1809, hlam]
                      · rcases h1bigk with h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c | h1811c
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          rcases p1811_3 (m.d 0 1) (by simp) with h1813 | h1813
                          · rcases p1811_3 (m.d 1 2) (by simp) with h1814 | h1814
                            · linarith only [h1814, hlam, p1811_0]
                            · rcases p1811_3 (m.d 1 3) (by simp) with h1816 | h1816
                              · linarith only [h1, h1816, hlam]
                              · linarith only [h1788, h1816, hlam]
                          · linarith only [h1813, hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1794, hc01, hlam, hphi, ht0b, ht45, ht5b, p1811_1, u4ehi3]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          rcases p1811_3 (m.d 0 1) (by simp) with h1821 | h1821
                          · rcases p1811_3 (m.d 1 2) (by simp) with h1822 | h1822
                            · linarith only [h0, h1822, hlam]
                            · rcases p1811_3 (m.d 1 3) (by simp) with h1824 | h1824
                              · linarith only [h1, h1824, hlam]
                              · linarith only [h1794, h1824, hlam]
                          · linarith only [h1821, hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          rcases p1811_3 (m.d 0 1) (by simp) with h1828 | h1828
                          · rcases p1811_3 (m.d 1 2) (by simp) with h1829 | h1829
                            · linarith only [h0, h1829, hlam]
                            · rcases p1811_3 (m.d 1 3) (by simp) with h1831 | h1831
                              · linarith only [h1, h1831, hlam]
                              · linarith only [h1795, h1831, hlam]
                          · linarith only [h1828, hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h0, hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1788, hlam, p1811_1]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1790, hlam, p1811_1]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1792, hlam, p1811_1]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1, hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          rcases p1811_3 (m.d 0 1) (by simp) with h1841 | h1841
                          · rcases p1811_3 (m.d 1 2) (by simp) with h1842 | h1842
                            · linarith only [h1788, h1842, hlam]
                            · rcases p1811_3 (m.d 1 3) (by simp) with h1844 | h1844
                              · rcases p1811_3 (m.d 1 4) (by simp) with h1845 | h1845
                                · linarith only [h1794, h1845, hlam]
                                · linarith only [h1790, h1845, hlam]
                              · linarith only [h1788, h1844, hlam]
                          · linarith only [h0, h1841, hlam]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1, h1794, hc01, hlam, hphi, ht0b, ht45, ht5b, p1811_1, u4ehi3]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1, h1794, h1796, hc01, hlam, hphi, ht0b, ht45, ht5b, p1811_1, u4ehi3]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h2, hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1635, h1787, h1796, h1806, hc12, hc23, hlam, hphi, p1811_1]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1794, hlam, p1811_1]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1796, hlam, p1811_1]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h3, hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1635, h1787, h1796, h1806, hc12, hc23, hlam, hphi, p1811_1]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1795, hlam, p1811_0]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [h1635, h1787, h1794, h1796, h1806, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1811_1, u4ehi3]
                        · have p1811_0 := h1811c.1
                          have p1811_1 := h1811c.2.1
                          have p1811_2 := h1811c.2.2.1
                          have p1811_3 := h1811c.2.2.2
                          linarith only [hlam, p1811_0]
                    · linarith only [h1635, h1787, h1808, hlam]
                  · linarith only [h1786, h1807, h4, hlam]
                · linarith only [h1, h1787, h1794, h1795, h1796, h1806, h4, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h1786, h1794, h1795, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1867 | h1867
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1868 | h1868
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1869 | h1869
                · linarith only [h1794, h1867, h1869, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1871 | h1871
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1872 | h1872
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1873 | h1873
                      · rcases h1bigk with h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          rcases p1874_3 (m.d 0 1) (by simp) with h1876 | h1876
                          · rcases p1874_3 (m.d 1 2) (by simp) with h1877 | h1877
                            · linarith only [h1877, hlam, p1874_0]
                            · rcases p1874_3 (m.d 1 3) (by simp) with h1879 | h1879
                              · linarith only [h1, h1879, hlam]
                              · linarith only [h1788, h1879, hlam]
                          · linarith only [h1876, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1867, hc01, hlam, hphi, ht0b, ht5b, p1874_1, u5ehi3]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1794, h1867, h1873, hc01, hlam, hphi, ht0b, ht45, ht5b, p1874_1, u4ehi4]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          rcases p1874_3 (m.d 0 1) (by simp) with h1885 | h1885
                          · rcases p1874_3 (m.d 1 2) (by simp) with h1886 | h1886
                            · linarith only [h0, h1886, hlam]
                            · rcases p1874_3 (m.d 1 3) (by simp) with h1888 | h1888
                              · linarith only [h1, h1888, hlam]
                              · linarith only [h1867, h1888, hlam]
                          · linarith only [h1885, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h0, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1788, hlam, p1874_1]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1790, hlam, p1874_1]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1792, hlam, p1874_1]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1, h1869, h4, hc12, hc34, hlam, hphi, ht23, p1874_1]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1794, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1, h1867, h1869, h1873, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1874_1, u4ehi4]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h2, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          rcases p1874_3 (m.d 0 1) (by simp) with h1903 | h1903
                          · rcases p1874_3 (m.d 1 2) (by simp) with h1904 | h1904
                            · linarith only [h1790, h1904, hlam]
                            · rcases p1874_3 (m.d 1 3) (by simp) with h1906 | h1906
                              · linarith only [h1794, h1906, hlam]
                              · linarith only [h1788, h1906, hlam]
                          · linarith only [h0, h1903, hlam]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1867, h1873, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1874_1, u4ehi4]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1867, h1873, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1874_1, u4ehi4]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h3, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1786, h1869, h3, h4, hc12, hc34, hlam, hphi, ht23, p1874_1]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1867, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [h1868, hlam, p1874_0]
                        · have p1874_0 := h1874c.1
                          have p1874_1 := h1874c.2.1
                          have p1874_2 := h1874c.2.2.1
                          have p1874_3 := h1874c.2.2.2
                          linarith only [hlam, p1874_0]
                      · linarith only [h1, h1867, h1869, h1873, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · linarith only [h1635, h1868, h1872, h2, hlam]
                  · linarith only [h1, h1867, h1871, h4, hlam]
              · linarith only [h1635, h1787, h1794, h1867, h1868, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1922 | h1922
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1923 | h1923
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1924 | h1924
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1925 | h1925
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1926 | h1926
                      · rcases h1bigk with h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          rcases p1927_3 (m.d 0 1) (by simp) with h1929 | h1929
                          · rcases p1927_3 (m.d 1 2) (by simp) with h1930 | h1930
                            · linarith only [h1930, hlam, p1927_0]
                            · rcases p1927_3 (m.d 1 3) (by simp) with h1932 | h1932
                              · linarith only [h1, h1932, hlam]
                              · linarith only [h1788, h1932, hlam]
                          · linarith only [h1929, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          rcases p1927_3 (m.d 0 1) (by simp) with h1936 | h1936
                          · rcases p1927_3 (m.d 1 2) (by simp) with h1937 | h1937
                            · linarith only [h0, h1937, hlam]
                            · rcases p1927_3 (m.d 1 3) (by simp) with h1939 | h1939
                              · linarith only [h1939, hlam, p1927_0]
                              · rcases p1927_3 (m.d 1 4) (by simp) with h1941 | h1941
                                · linarith only [h1941, h2, hlam]
                                · linarith only [h1794, h1941, hlam]
                          · linarith only [h1936, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1922, hc01, hlam, hphi, ht0b, ht45, ht5b, p1927_1, u4ehi4]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          rcases p1927_3 (m.d 0 1) (by simp) with h1946 | h1946
                          · rcases p1927_3 (m.d 1 2) (by simp) with h1947 | h1947
                            · linarith only [h0, h1947, hlam]
                            · rcases p1927_3 (m.d 1 3) (by simp) with h1949 | h1949
                              · linarith only [h1, h1949, hlam]
                              · rcases p1927_3 (m.d 1 4) (by simp) with h1951 | h1951
                                · linarith only [h1951, h2, hlam]
                                · linarith only [h1922, h1951, hlam]
                          · linarith only [h1946, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h0, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1788, hlam, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1790, hlam, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1792, hlam, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1794, hc12, hc34, hlam, hphi, ht23, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1794, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1867, hlam, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h2, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1794, h1923, hc12, hc23, hlam, hphi, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1788, h1794, h1923, hc12, hc23, hlam, hphi, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1794, h1923, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1927_1, u5ehi1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h3, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1786, h1867, h4, hc12, hc23, hlam, hphi, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1786, h1788, h1867, h4, hc12, hc23, hlam, hphi, p1927_1]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [h1922, hlam, p1927_0]
                        · have p1927_0 := h1927c.1
                          have p1927_1 := h1927c.2.1
                          have p1927_2 := h1927c.2.2.1
                          have p1927_3 := h1927c.2.2.2
                          linarith only [hlam, p1927_0]
                      · linarith only [h1635, h1787, h1788, h1794, h1923, h1926, hc12, hc23, hlam, hphi]
                    · linarith only [h1635, h1794, h1922, h1923, h1925, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · linarith only [h1786, h1924, h4, hlam]
                · linarith only [h1786, h1788, h1867, h1923, h4, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1979 | h1979
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1980 | h1980
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1981 | h1981
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1982 | h1982
                      · linarith only [h1922, h1979, h1982, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                      · linarith only [h1635, h1787, h1788, h1794, h1979, h1982, hc12, hc23, hlam, hphi]
                    · linarith only [h1635, h1787, h1981, hlam]
                  · linarith only [h1635, h1786, h1787, h1979, h1980, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                · linarith only [h1786, h1788, h1867, h1979, h4, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1988 | h1988
    · linarith only [h0, h1786, h1988, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1990 | h1990
      · linarith only [h0, h1635, h1990, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1992 | h1992
        · linarith only [h0, h1754, h1992, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1994 | h1994
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1995 | h1995
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1996 | h1996
              · linarith only [h1787, h1996, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1998 | h1998
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1999 | h1999
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2000 | h2000
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2001 | h2001
                      · linarith only [h1787, h1994, h2, h2001, hlam]
                      · rcases h1bigk with h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c | h2003c
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          rcases p2003_3 (m.d 0 1) (by simp) with h2005 | h2005
                          · rcases p2003_3 (m.d 1 2) (by simp) with h2006 | h2006
                            · linarith only [h2006, hlam, p2003_0]
                            · rcases p2003_3 (m.d 1 3) (by simp) with h2008 | h2008
                              · linarith only [h1, h2008, hlam]
                              · linarith only [h1988, h2008, hlam]
                          · linarith only [h2005, hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1995, h2001, hc01, hlam, hphi, ht0b, ht45, ht5b, p2003_1, u4ehi3]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          rcases p2003_3 (m.d 0 1) (by simp) with h2013 | h2013
                          · rcases p2003_3 (m.d 1 2) (by simp) with h2014 | h2014
                            · linarith only [h0, h2014, hlam]
                            · rcases p2003_3 (m.d 1 3) (by simp) with h2016 | h2016
                              · linarith only [h1, h2016, hlam]
                              · linarith only [h1994, h2016, hlam]
                          · linarith only [h2013, hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          rcases p2003_3 (m.d 0 1) (by simp) with h2020 | h2020
                          · rcases p2003_3 (m.d 1 2) (by simp) with h2021 | h2021
                            · linarith only [h0, h2021, hlam]
                            · rcases p2003_3 (m.d 1 3) (by simp) with h2023 | h2023
                              · linarith only [h1, h2023, hlam]
                              · linarith only [h1995, h2023, hlam]
                          · linarith only [h2020, hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h0, hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1988, hlam, p2003_1]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1990, hlam, p2003_1]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1992, hlam, p2003_1]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1, hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          rcases p2003_3 (m.d 0 1) (by simp) with h2033 | h2033
                          · rcases p2003_3 (m.d 1 2) (by simp) with h2034 | h2034
                            · linarith only [h1988, h2034, hlam]
                            · rcases p2003_3 (m.d 1 3) (by simp) with h2036 | h2036
                              · rcases p2003_3 (m.d 1 4) (by simp) with h2037 | h2037
                                · linarith only [h1994, h2037, hlam]
                                · linarith only [h1990, h2037, hlam]
                              · linarith only [h1988, h2036, hlam]
                          · linarith only [h0, h2033, hlam]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1, h1994, hc01, hlam, hphi, ht0b, ht45, ht5b, p2003_1, u4ehi3]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1, h1994, h1996, hc01, hlam, hphi, ht0b, ht45, ht5b, p2003_1, u4ehi3]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h2, hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1787, h1998, h2, h2000, hc12, hc23, hlam, hphi, p2003_1]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1994, hlam, p2003_1]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1996, hlam, p2003_1]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h3, hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1787, h1998, h2000, h3, hc12, hc23, hlam, hphi, p2003_1]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1995, hlam, p2003_0]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [h1787, h1994, h1998, h2000, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2003_1, u4ehi3]
                        · have p2003_0 := h2003c.1
                          have p2003_1 := h2003c.2.1
                          have p2003_2 := h2003c.2.2.1
                          have p2003_3 := h2003c.2.2.2
                          linarith only [hlam, p2003_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2055 | h2055
                      · linarith only [h0, h1635, h2000, h2055, hc12, hc34, hlam, hphi, ht23]
                      · rcases h1bigk with h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c | h2057c
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          rcases p2057_3 (m.d 0 1) (by simp) with h2059 | h2059
                          · rcases p2057_3 (m.d 1 2) (by simp) with h2060 | h2060
                            · linarith only [h2060, hlam, p2057_0]
                            · rcases p2057_3 (m.d 1 3) (by simp) with h2062 | h2062
                              · linarith only [h1, h2062, hlam]
                              · linarith only [h1988, h2062, hlam]
                          · linarith only [h2059, hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1994, hc01, hlam, hphi, ht0b, ht45, ht5b, p2057_1, u4ehi3]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          rcases p2057_3 (m.d 0 1) (by simp) with h2067 | h2067
                          · rcases p2057_3 (m.d 1 2) (by simp) with h2068 | h2068
                            · linarith only [h0, h2068, hlam]
                            · rcases p2057_3 (m.d 1 3) (by simp) with h2070 | h2070
                              · linarith only [h1, h2070, hlam]
                              · linarith only [h1994, h2070, hlam]
                          · linarith only [h2067, hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          rcases p2057_3 (m.d 0 1) (by simp) with h2074 | h2074
                          · rcases p2057_3 (m.d 1 2) (by simp) with h2075 | h2075
                            · linarith only [h0, h2075, hlam]
                            · rcases p2057_3 (m.d 1 3) (by simp) with h2077 | h2077
                              · linarith only [h1, h2077, hlam]
                              · linarith only [h1995, h2077, hlam]
                          · linarith only [h2074, hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h0, hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1988, hlam, p2057_1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1990, hlam, p2057_1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1992, hlam, p2057_1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1, hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          rcases p2057_3 (m.d 0 1) (by simp) with h2087 | h2087
                          · rcases p2057_3 (m.d 1 2) (by simp) with h2088 | h2088
                            · linarith only [h1988, h2088, hlam]
                            · rcases p2057_3 (m.d 1 3) (by simp) with h2090 | h2090
                              · rcases p2057_3 (m.d 1 4) (by simp) with h2091 | h2091
                                · linarith only [h1994, h2091, hlam]
                                · linarith only [h1990, h2091, hlam]
                              · linarith only [h1988, h2090, hlam]
                          · linarith only [h0, h2087, hlam]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p2057_1, u4ehi1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p2057_1, u5ehi1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h2, hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1635, h2, h2000, hc12, hc45, hlam, hphi, ht23, ht34, p2057_1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1994, hlam, p2057_1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1996, hlam, p2057_1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h3, hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          rcases p2057_3 (m.d 0 1) (by simp) with h2105 | h2105
                          · rcases p2057_3 (m.d 1 2) (by simp) with h2106 | h2106
                            · linarith only [h1992, h2106, hlam]
                            · rcases p2057_3 (m.d 1 3) (by simp) with h2108 | h2108
                              · rcases p2057_3 (m.d 1 4) (by simp) with h2109 | h2109
                                · linarith only [h1996, h2109, hlam]
                                · linarith only [h1990, h2109, hlam]
                              · linarith only [h1988, h2108, hlam]
                          · linarith only [h0, h2105, hlam]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h1995, hlam, p2057_0]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p2057_1, u4ehi1]
                        · have p2057_0 := h2057c.1
                          have p2057_1 := h2057c.2.1
                          have p2057_2 := h2057c.2.2.1
                          have p2057_3 := h2057c.2.2.2
                          linarith only [hlam, p2057_0]
                  · linarith only [h1786, h1999, h4, hlam]
                · linarith only [h1, h1994, h1998, h4, hlam]
            · linarith only [h1786, h1994, h1995, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2120 | h2120
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2121 | h2121
              · linarith only [h1787, h2, h2121, hlam]
              · linarith only [h1994, h2120, h2121, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2124 | h2124
              · linarith only [h1787, h2, h2124, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2126 | h2126
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2127 | h2127
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2128 | h2128
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2129 | h2129
                      · linarith only [h1787, h2, h2126, h2129, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                      · linarith only [h1988, h1994, h2128, h2129, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2132 | h2132
                      · linarith only [h2126, h2128, h2132, hlam]
                      · rcases h1bigk with h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c | h2134c
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          rcases p2134_3 (m.d 0 1) (by simp) with h2136 | h2136
                          · rcases p2134_3 (m.d 1 2) (by simp) with h2137 | h2137
                            · linarith only [h2137, hlam, p2134_0]
                            · rcases p2134_3 (m.d 1 3) (by simp) with h2139 | h2139
                              · linarith only [h1, h2139, hlam]
                              · linarith only [h1988, h2139, hlam]
                          · linarith only [h2136, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          rcases p2134_3 (m.d 0 1) (by simp) with h2143 | h2143
                          · rcases p2134_3 (m.d 1 2) (by simp) with h2144 | h2144
                            · linarith only [h0, h2144, hlam]
                            · rcases p2134_3 (m.d 1 3) (by simp) with h2146 | h2146
                              · linarith only [h2146, hlam, p2134_0]
                              · rcases p2134_3 (m.d 1 4) (by simp) with h2148 | h2148
                                · linarith only [h2, h2148, hlam]
                                · linarith only [h1994, h2148, hlam]
                          · linarith only [h2143, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          rcases p2134_3 (m.d 0 1) (by simp) with h2152 | h2152
                          · rcases p2134_3 (m.d 1 2) (by simp) with h2153 | h2153
                            · linarith only [h0, h2153, hlam]
                            · rcases p2134_3 (m.d 1 3) (by simp) with h2155 | h2155
                              · linarith only [h1, h2155, hlam]
                              · rcases p2134_3 (m.d 1 4) (by simp) with h2157 | h2157
                                · linarith only [h2157, hlam, p2134_0]
                                · rcases p2134_3 (m.d 1 5) (by simp) with h2159 | h2159
                                  · linarith only [h2159, h3, hlam]
                                  · linarith only [h2124, h2159, hlam]
                          · linarith only [h2152, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          rcases p2134_3 (m.d 0 1) (by simp) with h2163 | h2163
                          · rcases p2134_3 (m.d 1 2) (by simp) with h2164 | h2164
                            · linarith only [h0, h2164, hlam]
                            · rcases p2134_3 (m.d 1 3) (by simp) with h2166 | h2166
                              · linarith only [h1, h2166, hlam]
                              · rcases p2134_3 (m.d 1 4) (by simp) with h2168 | h2168
                                · linarith only [h2, h2168, hlam]
                                · rcases p2134_3 (m.d 1 5) (by simp) with h2170 | h2170
                                  · linarith only [h2170, hlam, p2134_0]
                                  · rcases h2bigk with h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p2172_1]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h4, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h1635, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h1754, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h0, hlam, p2172_1]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h1988, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h1990, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h1992, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      rcases p2172_3 (m.d 0 2) (by simp) with h2183 | h2183
                                      · linarith only [h2183, hlam, p2172_0]
                                      · rcases p2172_3 (m.d 1 2) (by simp) with h2185 | h2185
                                        · linarith only [h1988, h2185, hlam]
                                        · rcases p2172_3 (m.d 2 3) (by simp) with h2187 | h2187
                                          · rcases p2172_3 (m.d 2 4) (by simp) with h2188 | h2188
                                            · linarith only [h2126, h2188, hlam]
                                            · linarith only [h1635, h2188, hlam]
                                          · linarith only [h2187, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      rcases p2172_3 (m.d 0 2) (by simp) with h2192 | h2192
                                      · linarith only [h2192, h4, hlam]
                                      · linarith only [h0, h2192, hlam]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h1988, h1994, h2126, hc12, hc23, hlam, hphi, p2172_1]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h1754, hc02, hc23, hlam, hphi, p2172_1]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h0, h2128, hc12, hc45, hlam, hphi, ht23, ht34, p2172_1]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h2128, hc12, hc45, hlam, hphi, ht23, ht34, p2172_1]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h2126, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h2128, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      rcases p2172_3 (m.d 0 2) (by simp) with h2203 | h2203
                                      · linarith only [h2203, hlam, p2172_0]
                                      · rcases p2172_3 (m.d 1 2) (by simp) with h2205 | h2205
                                        · linarith only [h1992, h2205, hlam]
                                        · rcases p2172_3 (m.d 2 3) (by simp) with h2207 | h2207
                                          · rcases p2172_3 (m.d 2 4) (by simp) with h2208 | h2208
                                            · linarith only [h2128, h2208, hlam]
                                            · linarith only [h1635, h2208, hlam]
                                          · linarith only [h2207, h4, hlam]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      rcases p2172_3 (m.d 0 2) (by simp) with h2212 | h2212
                                      · linarith only [h1754, h2212, hlam]
                                      · linarith only [h0, h2212, hlam]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h2127, hlam, p2172_0]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [h0, h1635, hc12, hc25, hlam, hphi, p2172_1]
                                    · have p2172_0 := h2172c.1
                                      have p2172_1 := h2172c.2.1
                                      have p2172_2 := h2172c.2.2.1
                                      have p2172_3 := h2172c.2.2.2
                                      linarith only [hlam, p2172_0]
                          · linarith only [h2163, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h0, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1988, hlam, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1990, hlam, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1992, hlam, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1994, hc12, hc34, hlam, hphi, ht23, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1994, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h2120, hlam, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h2, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1787, h2, hc12, hc45, hlam, hphi, ht23, ht34, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1787, h2, hc13, hc45, hlam, hphi, ht34, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h2124, hlam, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h3, hlam, p2134_0]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1786, h2120, h4, hc12, hc23, hlam, hphi, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1786, h1988, h2120, h4, hc12, hc23, hlam, hphi, p2134_1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [h1786, h2120, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2134_1, u4ehi1]
                        · have p2134_0 := h2134c.1
                          have p2134_1 := h2134c.2.1
                          have p2134_2 := h2134c.2.2.1
                          have p2134_3 := h2134c.2.2.2
                          linarith only [hlam, p2134_0]
                  · linarith only [h1786, h2127, h4, hlam]
                · linarith only [h1786, h1988, h2120, h2126, h4, hc12, hc34, hlam, hphi, ht23]

end R2N4
