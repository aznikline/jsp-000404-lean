import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1449 | h1449
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1450 | h1450
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1451 | h1451
      · linarith only [h0, h1, h1451, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1453 | h1453
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1454 | h1454
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1455 | h1455
            · linarith only [h0, h1, h1451, h1455, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1457 | h1457
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1458 | h1458
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1459 | h1459
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1460 | h1460
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1461 | h1461
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1462 | h1462
                        · linarith only [h0, h1, h1455, h1457, h1462, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h1455, h1462, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1465 | h1465
                        · linarith only [h0, h1, h1455, h1457, h1465, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h1455, h1465, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1457, h1459, h1460, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h1, h1459, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1470 | h1470
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1471 | h1471
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1472 | h1472
                      · linarith only [h1457, h1458, h1472, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1474 | h1474
                        · linarith only [h1, h1450, h1457, h1458, h1474, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h1450, h1455, h1457, h1458, h1470, h1474, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h1, h1450, h1457, h1458, h1470, h1471, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h1450, h1457, h1458, h1470, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1479 | h1479
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1480 | h1480
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1481 | h1481
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1482 | h1482
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1483 | h1483
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1484 | h1484
                          · linarith only [h0, h1, h1455, h1479, h1484, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h1, h1449, h1455, h1457, h1484, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1449, h1455, h1480, h1483, hlam]
                      · linarith only [h1457, h1479, h1482, hlam]
                    · linarith only [h1, h1449, h1457, h1481, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1449, h1457, h1479, h1480, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1491 | h1491
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1492 | h1492
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1493 | h1493
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1494 | h1494
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1495 | h1495
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1496 | h1496
                            · rcases h1bigk with h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1, h1455, hc12, hc23, hlam, hphi, p1497_1]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1, h1492, h1493, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1497_1, u3ehi4]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1, h1455, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1497_1, u3ehi4]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h0, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1455, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1457, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1479, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h0, h1455, hc12, hc23, hlam, hphi, p1497_1]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                rcases p1497_3 (m.d 0 1) (by simp) with h1509 | h1509
                                · linarith only [h1, h1509, hlam]
                                · linarith only [h0, h1509, hlam]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                rcases p1497_3 (m.d 0 1) (by simp) with h1513 | h1513
                                · linarith only [h1, h1513, hlam]
                                · linarith only [h1449, h1513, hlam]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                rcases p1497_3 (m.d 0 1) (by simp) with h1516 | h1516
                                · linarith only [h1, h1516, hlam]
                                · linarith only [h1450, h1516, hlam]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1449, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1, h1449, h1455, hc12, hc23, hlam, hphi, p1497_1]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1491, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1449, h1492, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1497_1, u3ehi4]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1450, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1, h1450, h1455, hc12, hc23, hlam, hphi, p1497_1]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1492, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [h1493, hlam, p1497_0]
                              · have p1497_0 := h1497c.1
                                have p1497_1 := h1497c.2.1
                                have p1497_2 := h1497c.2.2.1
                                have p1497_3 := h1497c.2.2.2
                                linarith only [hlam, p1497_0]
                            · linarith only [h1, h1449, h1455, h1493, h1496, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1, h1449, h1455, h1493, h1495, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h1449, h1455, h1491, h1494, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1532 | h1532
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1533 | h1533
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1534 | h1534
                            · linarith only [h1491, h1493, h1534, hlam]
                            · rcases h1bigk with h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1, h1455, hc12, hc23, hlam, hphi, p1536_1]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1, h1455, h1457, hc12, hc23, hlam, hphi, p1536_1]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1, h1455, h1457, h1493, hc12, hc23, hlam, hphi, p1536_1]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h0, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1455, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1457, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1479, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h0, h1455, hc12, hc23, hlam, hphi, p1536_1]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                rcases p1536_3 (m.d 0 1) (by simp) with h1548 | h1548
                                · linarith only [h1, h1548, hlam]
                                · linarith only [h0, h1548, hlam]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                rcases p1536_3 (m.d 0 1) (by simp) with h1552 | h1552
                                · linarith only [h1, h1552, hlam]
                                · linarith only [h1449, h1552, hlam]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                rcases p1536_3 (m.d 0 1) (by simp) with h1555 | h1555
                                · linarith only [h1, h1555, hlam]
                                · linarith only [h1450, h1555, hlam]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1449, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1493, hc12, hc45, hlam, hphi, ht23, ht34, p1536_1]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1491, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1493, hlam, p1536_1]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1450, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1, h1450, h1455, hc12, hc23, hlam, hphi, p1536_1]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1492, hlam, p1536_0]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [h1, h1450, h1455, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1536_1]
                              · have p1536_0 := h1536c.1
                                have p1536_1 := h1536c.2.1
                                have p1536_2 := h1536c.2.2.1
                                have p1536_3 := h1536c.2.2.2
                                linarith only [hlam, p1536_0]
                          · linarith only [h1, h1450, h1455, h1492, h1533, hlam]
                        · linarith only [h1, h1450, h1455, h1491, h1493, h1532, hlam]
                    · linarith only [h0, h1, h1492, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1449, h1453, h1491, hlam]
          · linarith only [h1453, h1454, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1, h1449, h1453, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1574 | h1574
      · linarith only [h0, h1, h1574, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1576 | h1576
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1577 | h1577
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1578 | h1578
            · linarith only [h0, h1, h1574, h1578, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1580 | h1580
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1581 | h1581
                · linarith only [h0, h1450, h1581, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1583 | h1583
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1584 | h1584
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1585 | h1585
                      · linarith only [h0, h1450, h1580, h1585, hlam]
                      · linarith only [h0, h1450, h1580, h1583, h1585, hc45, hlam, hphi, ht34, u3ehi3]
                    · linarith only [h0, h1, h1577, h1580, h1583, h1584, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1, h1583, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1590 | h1590
                · linarith only [h1449, h1450, h1580, h1590, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1592 | h1592
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1593 | h1593
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1594 | h1594
                      · linarith only [h1449, h1450, h1594, hlam]
                      · linarith only [h1449, h1450, h1592, h1594, hc45, hlam, hphi, ht34, u3ehi3]
                    · linarith only [h1, h1577, h1593, hlam]
                  · linarith only [h1, h1577, h1592, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1576, h1577, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1, h1449, h1576, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1601 | h1601
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1602 | h1602
      · linarith only [h0, h1, h1602, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1604 | h1604
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1605 | h1605
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1606 | h1606
            · linarith only [h0, h1, h1602, h1606, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1608 | h1608
              · linarith only [h0, h1449, h1608, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1610 | h1610
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1611 | h1611
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1612 | h1612
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1613 | h1613
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1614 | h1614
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1615 | h1615
                          · linarith only [h0, h1449, h1606, h1610, h1611, h1615, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h1449, h1606, h1611, h1615, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1604, h1606, h1614, hlam]
                      · linarith only [h0, h1449, h1610, h1612, h1613, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h0, h1449, h1611, h1612, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1604, h1611, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1622 | h1622
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1623 | h1623
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1624 | h1624
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1625 | h1625
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1626 | h1626
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1627 | h1627
                            · rcases h1bigk with h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1449, h1608, hc12, hc24, hlam, hphi, p1628_1]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1449, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1449, h1623, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1628_1, u3ehi4]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h0, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1606, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1608, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1610, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h0, h1606, hc12, hc23, hlam, hphi, p1628_1]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                rcases p1628_3 (m.d 0 1) (by simp) with h1640 | h1640
                                · linarith only [h1, h1640, hlam]
                                · linarith only [h0, h1640, hlam]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1449, h1601, h1606, h1623, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1628_1, u3ehi4]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                rcases p1628_3 (m.d 0 1) (by simp) with h1645 | h1645
                                · linarith only [h1, h1645, hlam]
                                · linarith only [h1601, h1645, hlam]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1601, h1623, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1628_1, u3ehi4]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                rcases p1628_3 (m.d 0 1) (by simp) with h1649 | h1649
                                · linarith only [h1449, h1649, hlam]
                                · linarith only [h0, h1649, hlam]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1622, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                rcases p1628_3 (m.d 0 1) (by simp) with h1654 | h1654
                                · linarith only [h1449, h1654, hlam]
                                · linarith only [h1601, h1654, hlam]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1601, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1, h1601, h1606, hc12, hc23, hlam, hphi, p1628_1]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1623, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [h1624, hlam, p1628_0]
                              · have p1628_0 := h1628c.1
                                have p1628_1 := h1628c.2.1
                                have p1628_2 := h1628c.2.2.1
                                have p1628_3 := h1628c.2.2.2
                                linarith only [hlam, p1628_0]
                            · linarith only [h1449, h1601, h1608, h1624, h1625, h1627, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1449, h1608, h1625, h1626, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1449, h1601, h1606, h1622, h1623, h1625, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1449, h1601, h1623, h1624, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h1449, h1601, h1610, h1622, h1623, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1601, h1604, h1610, h1622, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1604, h1605, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1669 | h1669
          · linarith only [h1604, h1669, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1, h1601, h1669, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1672 | h1672
      · linarith only [h0, h1, h1672, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1674 | h1674
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1675 | h1675
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1676 | h1676
            · linarith only [h0, h1449, h1672, h1676, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1678 | h1678
              · linarith only [h0, h1449, h1678, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1680 | h1680
                · linarith only [h0, h1601, h1680, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1682 | h1682
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1683 | h1683
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1684 | h1684
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1685 | h1685
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1686 | h1686
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1687 | h1687
                            · rcases h1bigk with h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1601, h1680, hc12, hc25, hlam, hphi, p1688_1]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1449, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1601, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h0, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1676, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1678, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1680, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h0, h1676, hc12, hc23, hlam, hphi, p1688_1]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                rcases p1688_3 (m.d 0 1) (by simp) with h1700 | h1700
                                · linarith only [h1, h1700, hlam]
                                · linarith only [h0, h1700, hlam]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h0, h1449, h1676, hc12, hc23, hlam, hphi, p1688_1]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h0, h1601, h1676, hc12, hc23, hlam, hphi, p1688_1]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h0, h1678, hc12, hc24, hlam, hphi, p1688_1]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                rcases p1688_3 (m.d 0 1) (by simp) with h1707 | h1707
                                · linarith only [h1449, h1707, hlam]
                                · linarith only [h0, h1707, hlam]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1682, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h0, h1601, h1676, h1682, hc12, hc23, hlam, hphi, p1688_1]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h0, h1680, h1686, hc12, hc23, hlam, hphi, p1688_1]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                rcases p1688_3 (m.d 0 1) (by simp) with h1714 | h1714
                                · linarith only [h1601, h1714, hlam]
                                · linarith only [h0, h1714, hlam]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1683, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [h1684, hlam, p1688_0]
                              · have p1688_0 := h1688c.1
                                have p1688_1 := h1688c.2.1
                                have p1688_2 := h1688c.2.2.1
                                have p1688_3 := h1688c.2.2.2
                                linarith only [hlam, p1688_0]
                            · rcases h1bigk with h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1, h1676, hc12, hc23, hlam, hphi, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1449, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1601, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h0, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1676, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1678, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1680, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h0, h1676, hc12, hc23, hlam, hphi, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                rcases p1720_3 (m.d 0 1) (by simp) with h1732 | h1732
                                · linarith only [h1, h1732, hlam]
                                · linarith only [h0, h1732, hlam]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1676, h1684, h1687, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h0, h1601, h1676, hc12, hc23, hlam, hphi, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h0, h1678, h1685, hc12, hc23, hlam, hphi, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                rcases p1720_3 (m.d 0 1) (by simp) with h1739 | h1739
                                · linarith only [h1449, h1739, hlam]
                                · linarith only [h0, h1739, hlam]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1682, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h0, h1601, h1678, h1685, hc12, hc23, hlam, hphi, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h0, h1680, h1686, hc12, hc23, hlam, hphi, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                rcases p1720_3 (m.d 0 1) (by simp) with h1746 | h1746
                                · linarith only [h1601, h1746, hlam]
                                · linarith only [h0, h1746, hlam]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1683, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1684, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                          · linarith only [h0, h1, h1676, h1686, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1601, h1676, h1682, h1684, h1685, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1449, h1684, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1, h1675, h1683, hlam]
                  · linarith only [h1, h1674, h1682, hlam]
          · linarith only [h1674, h1675, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1758 | h1758
          · linarith only [h1674, h1758, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1760 | h1760
            · linarith only [h0, h1449, h1760, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1762 | h1762
              · linarith only [h0, h1449, h1762, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1764 | h1764
                · linarith only [h0, h1601, h1764, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1766 | h1766
                  · linarith only [h0, h1, h1674, h1760, h1766, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1766, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_23_L_I_M_IR_x0_x0 m hb1 hb3 h0 h1
  · exact r1l7_11_23_L_I_M_IR_x0_x1 m hb1 hb3 h0 h1

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1769 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1770 | h1770
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1771 | h1771
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1772 | h1772
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1773 | h1773
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1774 | h1774
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1775 | h1775
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1776 | h1776
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1777 | h1777
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1778 | h1778
                  · linarith only [h0, h1769, h1778, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1769, h1773, h1775, h1778, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1769, h1773, h1777, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h0, h1769, h1773, h1776, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h1769, h1773, h1775, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h1773, h1774, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1785 | h1785
          · linarith only [h1773, h1785, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1787 | h1787
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1788 | h1788
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1789 | h1789
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1790 | h1790
                  · linarith only [h1769, h1773, h1790, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1792 | h1792
                    · linarith only [h1769, h1785, h1792, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1794 | h1794
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1795 | h1795
                        · linarith only [h1769, h1773, h1787, h1795, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1797 | h1797
                          · linarith only [h1769, h1785, h1787, h1797, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1799 | h1799
                            · rcases h1bigk with h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c | h1800c
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h0, hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h0, h1787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1800_1, u3ehi2]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h0, h1794, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1800_1]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h0, h1787, h1792, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1800_1, u3ehi2]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1769, h1787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1800_1, u3ehi2]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                rcases p1800_3 (m.d 0 1) (by simp) with h1808 | h1808
                                · linarith only [h0, h1808, hlam]
                                · linarith only [h1769, h1808, hlam]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                rcases p1800_3 (m.d 0 1) (by simp) with h1811 | h1811
                                · linarith only [h0, h1811, hlam]
                                · linarith only [h1770, h1811, hlam]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                rcases p1800_3 (m.d 0 1) (by simp) with h1814 | h1814
                                · linarith only [h0, h1814, hlam]
                                · linarith only [h1771, h1814, hlam]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1769, hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1787, hlam, p1800_1]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1790, hlam, p1800_1]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1792, hlam, p1800_1]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1770, hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1788, hlam, p1800_1]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1770, h1787, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1800_1, u3ehi2]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h0, h1770, h1787, h1792, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1800_1, u3ehi2]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1771, hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1789, hlam, p1800_1]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h0, h1771, h1787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1800_1, u3ehi2]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [h1794, hlam, p1800_0]
                              · have p1800_0 := h1800c.1
                                have p1800_1 := h1800c.2.1
                                have p1800_2 := h1800c.2.2.1
                                have p1800_3 := h1800c.2.2.2
                                linarith only [hlam, p1800_0]
                            · linarith only [h1769, h1773, h1787, h1799, hc45, hlam, hphi, ht34, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1833 | h1833
                        · linarith only [h1769, h1773, h1787, h1833, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1835 | h1835
                          · linarith only [h1769, h1785, h1787, h1835, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1837 | h1837
                            · linarith only [h1787, h1790, h1794, h1837, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1769, h1773, h1787, h1837, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h1769, h1787, h1789, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1769, h1787, h1788, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1769, h1787, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h0, h1769, h1772, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1844 | h1844
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1845 | h1845
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1846 | h1846
          · linarith only [h1769, h1771, h1846, hlam]
          · linarith only [h1845, h1846, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1849 | h1849
          · linarith only [h1845, h1849, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1851 | h1851
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1852 | h1852
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1853 | h1853
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1854 | h1854
                  · linarith only [h1769, h1771, h1845, h1853, h1854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1856 | h1856
                    · linarith only [h1769, h1845, h1856, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1770, h1771, h1851, h1854, h1856, hc35, hlam, hphi, u3ehi2]
                · linarith only [h0, h1769, h1851, h1853, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1769, h1851, h1852, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1769, h1851, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h0, h1769, h1844, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1863 | h1863
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1864 | h1864
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1865 | h1865
        · linarith only [h1769, h1770, h1865, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1867 | h1867
          · linarith only [h1865, h1867, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1869 | h1869
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1870 | h1870
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1871 | h1871
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1872 | h1872
                  · linarith only [h1769, h1865, h1872, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1769, h1770, h1869, h1872, hc34, hlam, hphi, u3ehi2]
                · linarith only [h1769, h1770, h1869, h1870, h1871, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1769, h1869, h1870, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1769, h1869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h0, h1769, h1864, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1879 | h1879
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1880 | h1880
        · linarith only [h1769, h1770, h1880, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1882 | h1882
          · linarith only [h1880, h1882, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1884 | h1884
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1885 | h1885
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1886 | h1886
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1887 | h1887
                  · linarith only [h1769, h1880, h1887, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1769, h1770, h1884, h1887, hc34, hlam, hphi, u3ehi2]
                · linarith only [h1769, h1770, h1884, h1885, h1886, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1769, h1884, h1885, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1769, h1884, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h0, h1769, h1879, hlam]

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1769 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1894 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1895 | h1895
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1896 | h1896
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1897 | h1897
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1898 | h1898
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1899 | h1899
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1900 | h1900
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1901 | h1901
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1902 | h1902
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1903 | h1903
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1904 | h1904
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1905 | h1905
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1906 | h1906
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1907 | h1907
                          · rcases h1bigk with h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h0, hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1769, hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1769, h1899, h1901, h1904, h1906, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1908_1, u3ehi4]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1769, h1899, h1901, h1906, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1908_1, u3ehi4]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1894, h1901, h1904, h1906, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1908_1, u3ehi4]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1769, hc01, hc12, hlam, hphi, p1908_1]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              rcases p1908_3 (m.d 0 1) (by simp) with h1917 | h1917
                              · linarith only [h0, h1917, hlam]
                              · linarith only [h1894, h1917, hlam]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              rcases p1908_3 (m.d 0 1) (by simp) with h1920 | h1920
                              · linarith only [h0, h1920, hlam]
                              · linarith only [h1895, h1920, hlam]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1894, h1901, h1904, h1906, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1908_1, u3ehi4]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1899, hlam, p1908_1]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              rcases p1908_3 (m.d 0 1) (by simp) with h1926 | h1926
                              · linarith only [h1769, h1926, hlam]
                              · linarith only [h1894, h1926, hlam]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              rcases p1908_3 (m.d 0 1) (by simp) with h1929 | h1929
                              · linarith only [h1769, h1929, hlam]
                              · linarith only [h1895, h1929, hlam]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1894, hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1900, hlam, p1908_1]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1902, hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1894, h1901, h1906, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1908_1, u3ehi4]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1895, hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1901, hlam, p1908_1]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1903, hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [h1904, hlam, p1908_0]
                            · have p1908_0 := h1908c.1
                              have p1908_1 := h1908c.2.1
                              have p1908_2 := h1908c.2.2.1
                              have p1908_3 := h1908c.2.2.2
                              linarith only [hlam, p1908_0]
                          · linarith only [h1769, h1894, h1899, h1904, h1907, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1905, h1906, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1769, h1894, h1899, h1902, h1905, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1945 | h1945
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1946 | h1946
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1947 | h1947
                          · linarith only [h1900, h1904, h1945, h1947, hlam]
                          · rcases h1bigk with h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h0, hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1769, hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1769, h1899, h1900, h1945, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1769, h1899, h1903, h1947, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1894, h1900, h1945, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1769, hc01, hc12, hlam, hphi, p1949_1]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              rcases p1949_3 (m.d 0 1) (by simp) with h1958 | h1958
                              · linarith only [h0, h1958, hlam]
                              · linarith only [h1894, h1958, hlam]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              rcases p1949_3 (m.d 0 1) (by simp) with h1961 | h1961
                              · linarith only [h0, h1961, hlam]
                              · linarith only [h1895, h1961, hlam]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1895, h1900, h1904, h1945, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1899, hlam, p1949_1]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              rcases p1949_3 (m.d 0 1) (by simp) with h1967 | h1967
                              · linarith only [h1769, h1967, hlam]
                              · linarith only [h1894, h1967, hlam]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              rcases p1949_3 (m.d 0 1) (by simp) with h1970 | h1970
                              · linarith only [h1769, h1970, hlam]
                              · linarith only [h1895, h1970, hlam]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1894, hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1900, hlam, p1949_1]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1902, hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1904, hlam, p1949_1]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1895, hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1901, hlam, p1949_1]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1903, hlam, p1949_0]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [h1895, h1900, h1945, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                            · have p1949_0 := h1949c.1
                              have p1949_1 := h1949c.2.1
                              have p1949_2 := h1949c.2.2.1
                              have p1949_3 := h1949c.2.2.2
                              linarith only [hlam, p1949_0]
                        · linarith only [h1769, h1895, h1899, h1903, h1946, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1769, h1894, h1899, h1902, h1945, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h1769, h1894, h1902, h1903, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1769, h1895, h1898, h1902, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1769, h1895, h1899, h1901, hlam]
            · linarith only [h1769, h1894, h1899, h1900, hlam]
          · linarith only [h0, h1896, h1899, hlam]
        · linarith only [h1897, h1898, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1769, h1894, h1897, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1992 | h1992
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1993 | h1993
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1994 | h1994
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1995 | h1995
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1996 | h1996
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1997 | h1997
                · linarith only [h0, h1894, h1896, h1994, h1997, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h1894, h1896, h1992, h1994, h1997, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1894, h1896, h1992, h1994, h1996, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h1894, h1896, h1992, h1994, h1995, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2002 | h2002
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2003 | h2003
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2004 | h2004
                · linarith only [h0, h1894, h1994, h2004, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1769, h1895, h1993, h2004, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1895, h2003, hlam]
            · linarith only [h0, h1894, h2002, hlam]
        · linarith only [h1992, h1993, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1769, h1894, h1992, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2011 | h2011
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2012 | h2012
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2013 | h2013
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2014 | h2014
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2015 | h2015
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2016 | h2016
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2017 | h2017
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2018 | h2018
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2019 | h2019
                    · linarith only [h1894, h1895, h2019, hlam]
                    · linarith only [h1894, h1895, h2017, h2019, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h0, h1769, h1894, h2011, h2013, h2017, h2018, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1769, h2013, h2017, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2024 | h2024
                · linarith only [h0, h1894, h2016, h2024, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1769, h2013, h2024, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h1894, h2015, hlam]
          · linarith only [h0, h2011, h2014, hlam]
        · linarith only [h2012, h2013, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1769, h1894, h2012, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2031 | h2031
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2032 | h2032
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2033 | h2033
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2034 | h2034
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2035 | h2035
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2036 | h2036
                · linarith only [h0, h1894, h2011, h2033, h2036, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1769, h2032, h2036, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1894, h2011, h2031, h2033, h2035, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h1894, h2011, h2031, h2033, h2034, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2041 | h2041
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2042 | h2042
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2043 | h2043
                · linarith only [h0, h1894, h2033, h2043, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1894, h1895, h2031, h2033, h2042, h2043, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2046 | h2046
                · linarith only [h0, h1894, h2033, h2046, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1769, h2031, h2046, hlam]
            · linarith only [h0, h1894, h2041, hlam]
        · linarith only [h2031, h2032, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1769, h1894, h2031, hlam]

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1769 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1894 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2052 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2053 | h2053
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2054 | h2054
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2055 | h2055
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2056 | h2056
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2057 | h2057
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2058 | h2058
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2059 | h2059
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2060 | h2060
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2061 | h2061
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2062 | h2062
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2063 | h2063
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2064 | h2064
                        · rcases h1bigk with h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c | h2065c
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h0, hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h1769, hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h1894, hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h1894, h2056, h2058, h2059, h2063, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2065_1, u3ehi4]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2052, h2058, h2063, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2065_1, u3ehi4]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h1769, hc01, hc12, hlam, hphi, p2065_1]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h1894, h2052, h2058, h2063, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2065_1, u3ehi4]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            rcases p2065_3 (m.d 0 1) (by simp) with h2075 | h2075
                            · linarith only [h0, h2075, hlam]
                            · linarith only [h2052, h2075, hlam]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2052, h2058, h2063, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2065_1, u3ehi4]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2056, hlam, p2065_1]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h1894, h2052, h2056, h2058, h2063, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2065_1, u3ehi4]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            rcases p2065_3 (m.d 0 1) (by simp) with h2082 | h2082
                            · linarith only [h1769, h2082, hlam]
                            · linarith only [h2052, h2082, hlam]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2052, h2058, h2063, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2065_1, u3ehi4]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2057, hlam, p2065_1]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2059, hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            rcases p2065_3 (m.d 0 1) (by simp) with h2089 | h2089
                            · linarith only [h1894, h2089, hlam]
                            · linarith only [h2052, h2089, hlam]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2052, hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2058, hlam, p2065_1]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2060, hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [h2061, hlam, p2065_0]
                          · have p2065_0 := h2065c.1
                            have p2065_1 := h2065c.2.1
                            have p2065_2 := h2065c.2.2.1
                            have p2065_3 := h2065c.2.2.2
                            linarith only [hlam, p2065_0]
                        · linarith only [h0, h2052, h2061, h2064, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1894, h2052, h2056, h2059, h2060, h2063, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2099 | h2099
                      · linarith only [h2054, h2062, h2099, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1894, h2052, h2056, h2059, h2060, h2099, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h1894, h2052, h2060, h2061, hc45, hlam, hphi, ht34, u3ehi4]
                · linarith only [h1894, h2052, h2055, h2059, h2060, hlam]
              · linarith only [h1769, h2052, h2054, h2055, h2059, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
            · linarith only [h1769, h2052, h2056, h2058, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2106 | h2106
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2107 | h2107
              · linarith only [h2056, h2057, h2107, hlam]
              · linarith only [h0, h1769, h2052, h2053, h2054, h2055, h2057, h2107, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
            · linarith only [h0, h2052, h2106, hlam]
        · linarith only [h0, h2053, h2056, hlam]
      · linarith only [h2054, h2055, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2113 | h2113
      · linarith only [h2054, h2113, hc34, hlam, hphi, u3ehi4]
      · linarith only [h1769, h2052, h2113, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2116 | h2116
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2117 | h2117
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2118 | h2118
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2119 | h2119
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2120 | h2120
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2121 | h2121
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2122 | h2122
                · linarith only [h0, h2052, h2053, h2118, h2122, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1769, h2116, h2122, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h2052, h2053, h2116, h2118, h2121, hc03, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h2053, h2116, h2118, h2120, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h0, h2052, h2053, h2117, h2118, h2119, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2128 | h2128
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2129 | h2129
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2130 | h2130
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2131 | h2131
                · linarith only [h0, h2052, h2118, h2131, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1769, h2116, h2131, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1769, h2116, h2130, hlam]
            · linarith only [h1894, h2052, h2128, h2129, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2136 | h2136
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2137 | h2137
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2138 | h2138
                · linarith only [h0, h2052, h2118, h2138, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1769, h2116, h2138, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1769, h2116, h2137, hlam]
            · linarith only [h0, h2052, h2136, hlam]
      · linarith only [h2116, h2117, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2144 | h2144
      · linarith only [h2116, h2144, hc34, hlam, hphi, u3ehi4]
      · linarith only [h1769, h2052, h2144, hlam]

end R2N4
