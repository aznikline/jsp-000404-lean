import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1290 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1381 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h1435 | h1435
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1436 | h1436
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1437 | h1437
      · linarith only [h0, h1437, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1439 | h1439
        · linarith only [h0, h1290, h1439, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1441 | h1441
          · linarith only [h0, h1381, h1441, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1443 | h1443
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1444 | h1444
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1445 | h1445
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1446 | h1446
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1447 | h1447
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1448 | h1448
                      · linarith only [h1, h1443, h1448, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h1444, h1448, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h1, h1443, h1444, h1447, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1452 | h1452
                    · linarith only [h1445, h1446, h1452, hlam]
                    · linarith only [h0, h1290, h1435, h1436, h1444, h1446, h1452, h3, h4, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1435, h1445, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1456 | h1456
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1457 | h1457
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1458 | h1458
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1459 | h1459
                      · linarith only [h1443, h1444, h1459, hlam]
                      · rcases h2bigk with h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p1461_1]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h4, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1290, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1381, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h0, hlam, p1461_1]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1437, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1439, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1441, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          rcases p1461_3 (m.d 0 2) (by simp) with h1472 | h1472
                          · linarith only [h1472, hlam, p1461_0]
                          · rcases p1461_3 (m.d 1 2) (by simp) with h1474 | h1474
                            · linarith only [h1437, h1474, hlam]
                            · rcases p1461_3 (m.d 2 3) (by simp) with h1476 | h1476
                              · rcases p1461_3 (m.d 2 4) (by simp) with h1477 | h1477
                                · linarith only [h1456, h1477, hlam]
                                · linarith only [h1290, h1477, hlam]
                              · linarith only [h1476, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          rcases p1461_3 (m.d 0 2) (by simp) with h1481 | h1481
                          · linarith only [h1481, h4, hlam]
                          · linarith only [h0, h1481, hlam]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1290, hc02, hc23, hlam, hphi, p1461_1]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h0, h1381, hc12, hc23, hlam, hphi, p1461_1]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          rcases p1461_3 (m.d 0 2) (by simp) with h1487 | h1487
                          · linarith only [h1487, hlam, p1461_0]
                          · rcases p1461_3 (m.d 1 2) (by simp) with h1489 | h1489
                            · linarith only [h1439, h1489, hlam]
                            · rcases p1461_3 (m.d 2 3) (by simp) with h1491 | h1491
                              · rcases p1461_3 (m.d 2 4) (by simp) with h1492 | h1492
                                · rcases p1461_3 (m.d 2 5) (by simp) with h1493 | h1493
                                  · linarith only [h1458, h1493, hlam]
                                  · linarith only [h1381, h1493, hlam]
                                · linarith only [h1492, hlam, p1461_0]
                              · linarith only [h1491, h4, hlam]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          rcases p1461_3 (m.d 0 2) (by simp) with h1498 | h1498
                          · linarith only [h1290, h1498, hlam]
                          · linarith only [h0, h1498, hlam]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1456, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1381, h1436, h1444, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1461_1, u4ehi1]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          rcases p1461_3 (m.d 0 2) (by simp) with h1504 | h1504
                          · linarith only [h1504, hlam, p1461_0]
                          · rcases p1461_3 (m.d 1 2) (by simp) with h1506 | h1506
                            · linarith only [h1441, h1506, hlam]
                            · rcases p1461_3 (m.d 2 3) (by simp) with h1508 | h1508
                              · rcases p1461_3 (m.d 2 4) (by simp) with h1509 | h1509
                                · rcases p1461_3 (m.d 2 5) (by simp) with h1510 | h1510
                                  · rcases h4bigk with h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      rcases p1511_3 (m.d 0 4) (by simp) with h1513 | h1513
                                      · rcases p1511_3 (m.d 1 4) (by simp) with h1514 | h1514
                                        · linarith only [h1514, h2, hlam]
                                        · rcases p1511_3 (m.d 2 4) (by simp) with h1516 | h1516
                                          · rcases p1511_3 (m.d 3 4) (by simp) with h1517 | h1517
                                            · linarith only [h1435, h1517, hlam]
                                            · rcases p1511_3 (m.d 4 5) (by simp) with h1519 | h1519
                                              · linarith only [h1436, h1519, hlam]
                                              · linarith only [h1444, h1519, hlam]
                                          · linarith only [h1439, h1516, hlam]
                                      · linarith only [h1513, h2, hlam]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1290, hlam, p1511_1]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      rcases p1511_3 (m.d 0 4) (by simp) with h1525 | h1525
                                      · rcases p1511_3 (m.d 1 4) (by simp) with h1526 | h1526
                                        · linarith only [h1526, h2, hlam]
                                        · linarith only [h1443, h1526, hlam]
                                      · linarith only [h1435, h1525, hlam]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1435, h1443, h1444, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1511_1, u4ehi3]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h2, hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1439, hlam, p1511_1]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1436, h1444, hc05, hlam, hphi, ht0b, ht45, ht5b, p1511_1, u4ehi3]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1444, hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1436, h1456, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1511_1, u4ehi4]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      rcases p1511_3 (m.d 0 4) (by simp) with h1537 | h1537
                                      · linarith only [h1290, h1537, hlam]
                                      · linarith only [h1537, h2, hlam]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      rcases p1511_3 (m.d 0 4) (by simp) with h1541 | h1541
                                      · linarith only [h1290, h1541, hlam]
                                      · linarith only [h1435, h1541, hlam]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1443, h1444, h1456, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1511_1, u4ehi3]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1435, hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1443, hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1456, hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1459, hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1436, hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1436, h1443, hc04, hlam, hphi, ht0b, ht45, ht5b, p1511_1, u4ehi3]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1458, hlam, p1511_0]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [h1290, h1436, h1456, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1511_1, u4ehi3]
                                    · have p1511_0 := h1511c.1
                                      have p1511_1 := h1511c.2.1
                                      have p1511_2 := h1511c.2.2.1
                                      have p1511_3 := h1511c.2.2.2
                                      linarith only [hlam, p1511_0]
                                  · linarith only [h1510, hlam, p1461_0]
                                · linarith only [h1290, h1509, hlam]
                              · linarith only [h1508, h4, hlam]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          rcases p1461_3 (m.d 0 2) (by simp) with h1558 | h1558
                          · linarith only [h1381, h1558, hlam]
                          · linarith only [h0, h1558, hlam]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1457, hlam, p1461_0]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [h1458, hlam, p1461_1]
                        · have p1461_0 := h1461c.1
                          have p1461_1 := h1461c.2.1
                          have p1461_2 := h1461c.2.2.1
                          have p1461_3 := h1461c.2.2.2
                          linarith only [hlam, p1461_0]
                    · linarith only [h1290, h1436, h1458, hlam]
                  · linarith only [h1290, h1436, h1443, h1444, h1456, h1457, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · linarith only [h1435, h1436, h1443, h1444, h1456, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1567 | h1567
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1568 | h1568
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1569 | h1569
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1570 | h1570
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1571 | h1571
                      · rcases h2bigk with h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p1572_1]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h4, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1290, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1381, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h0, hlam, p1572_1]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1437, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1439, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1441, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          rcases p1572_3 (m.d 0 2) (by simp) with h1583 | h1583
                          · linarith only [h1583, hlam, p1572_0]
                          · rcases p1572_3 (m.d 1 2) (by simp) with h1585 | h1585
                            · linarith only [h1437, h1585, hlam]
                            · rcases p1572_3 (m.d 2 3) (by simp) with h1587 | h1587
                              · rcases p1572_3 (m.d 2 4) (by simp) with h1588 | h1588
                                · linarith only [h1568, h1588, hlam]
                                · linarith only [h1290, h1588, hlam]
                              · linarith only [h1587, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          rcases p1572_3 (m.d 0 2) (by simp) with h1592 | h1592
                          · linarith only [h1592, h4, hlam]
                          · linarith only [h0, h1592, hlam]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1290, h1435, h1443, h1567, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1572_1, u4ehi4]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1381, hc02, hc23, hlam, hphi, p1572_1]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          rcases p1572_3 (m.d 0 2) (by simp) with h1598 | h1598
                          · linarith only [h1598, hlam, p1572_0]
                          · rcases p1572_3 (m.d 1 2) (by simp) with h1600 | h1600
                            · linarith only [h1439, h1600, hlam]
                            · rcases p1572_3 (m.d 2 3) (by simp) with h1602 | h1602
                              · rcases p1572_3 (m.d 2 4) (by simp) with h1603 | h1603
                                · rcases p1572_3 (m.d 2 5) (by simp) with h1604 | h1604
                                  · linarith only [h1570, h1604, hlam]
                                  · linarith only [h1381, h1604, hlam]
                                · linarith only [h1603, hlam, p1572_0]
                              · linarith only [h1602, h4, hlam]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          rcases p1572_3 (m.d 0 2) (by simp) with h1609 | h1609
                          · linarith only [h1290, h1609, hlam]
                          · linarith only [h0, h1609, hlam]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1568, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h0, h1381, hc12, hc24, hlam, hphi, p1572_1]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          rcases p1572_3 (m.d 0 2) (by simp) with h1615 | h1615
                          · linarith only [h1615, hlam, p1572_0]
                          · rcases p1572_3 (m.d 1 2) (by simp) with h1617 | h1617
                            · linarith only [h1441, h1617, hlam]
                            · rcases p1572_3 (m.d 2 3) (by simp) with h1619 | h1619
                              · rcases p1572_3 (m.d 2 4) (by simp) with h1620 | h1620
                                · rcases p1572_3 (m.d 2 5) (by simp) with h1621 | h1621
                                  · rcases h4bigk with h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1567, hc04, hlam, hphi, ht0b, ht45, ht5b, p1622_1, u4ehi4]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1290, hlam, p1622_1]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1290, h1443, h1567, h1568, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1622_1, u4ehi4]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      rcases p1622_3 (m.d 0 4) (by simp) with h1627 | h1627
                                      · rcases p1622_3 (m.d 1 4) (by simp) with h1628 | h1628
                                        · linarith only [h1628, h2, hlam]
                                        · linarith only [h1567, h1628, hlam]
                                      · linarith only [h1627, hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h2, hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1439, hlam, p1622_1]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1443, hlam, p1622_1]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1622_1, u4ehi4]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1436, h1568, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1622_1, u4ehi4]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1567, h1568, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1622_1, u4ehi4]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1443, h1567, h1568, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1622_1, u4ehi4]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      rcases p1622_3 (m.d 0 4) (by simp) with h1641 | h1641
                                      · linarith only [h1290, h1641, hlam]
                                      · linarith only [h1436, h1641, hlam]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1435, hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1435, h1567, hc04, hlam, hphi, ht0b, ht45, ht5b, p1622_1, u4ehi4]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1568, hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1435, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1622_1, u4ehi4]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1436, hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1567, hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1570, hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [h1571, hlam, p1622_0]
                                    · have p1622_0 := h1622c.1
                                      have p1622_1 := h1622c.2.1
                                      have p1622_2 := h1622c.2.2.1
                                      have p1622_3 := h1622c.2.2.2
                                      linarith only [hlam, p1622_0]
                                  · linarith only [h1621, hlam, p1572_0]
                                · linarith only [h1290, h1620, hlam]
                              · linarith only [h1619, h4, hlam]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          rcases p1572_3 (m.d 0 2) (by simp) with h1657 | h1657
                          · linarith only [h1381, h1657, hlam]
                          · linarith only [h0, h1657, hlam]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1569, hlam, p1572_0]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [h1570, hlam, p1572_1]
                        · have p1572_0 := h1572c.1
                          have p1572_1 := h1572c.2.1
                          have p1572_2 := h1572c.2.2.1
                          have p1572_3 := h1572c.2.2.2
                          linarith only [hlam, p1572_0]
                      · linarith only [h1443, h1567, h1571, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1290, h1435, h1443, h1567, h1570, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · linarith only [h1435, h1443, h1567, h1569, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · linarith only [h1435, h1568, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1667 | h1667
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1668 | h1668
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1669 | h1669
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1670 | h1670
                      · linarith only [h1435, h1567, h1670, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                      · linarith only [h1435, h1436, h1437, h1443, h1670, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1290, h1435, h1436, h1669, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h1435, h1437, h1443, h1668, h4, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1435, h1436, h1567, h1667, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1676 | h1676
      · linarith only [h0, h1435, h1676, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1678 | h1678
        · linarith only [h0, h1290, h1678, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1680 | h1680
          · linarith only [h0, h1381, h1680, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1682 | h1682
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1683 | h1683
              · linarith only [h1436, h1683, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1685 | h1685
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1686 | h1686
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1687 | h1687
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1688 | h1688
                      · linarith only [h1436, h1682, h1688, h2, hlam]
                      · rcases h2bigk with h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1290, h1436, h1685, h1687, hc12, hc23, hlam, hphi, p1690_1]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h4, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1290, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1381, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h0, hlam, p1690_1]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1676, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1678, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1680, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          rcases p1690_3 (m.d 0 2) (by simp) with h1701 | h1701
                          · linarith only [h1701, hlam, p1690_0]
                          · rcases p1690_3 (m.d 1 2) (by simp) with h1703 | h1703
                            · linarith only [h1676, h1703, hlam]
                            · rcases p1690_3 (m.d 2 3) (by simp) with h1705 | h1705
                              · rcases p1690_3 (m.d 2 4) (by simp) with h1706 | h1706
                                · linarith only [h1685, h1706, hlam]
                                · linarith only [h1290, h1706, hlam]
                              · linarith only [h1705, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          rcases p1690_3 (m.d 0 2) (by simp) with h1710 | h1710
                          · linarith only [h1710, h4, hlam]
                          · linarith only [h0, h1710, hlam]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1436, h1682, h1687, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1690_1, u4ehi3]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1436, h1682, h1687, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1690_1, u4ehi3]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          rcases p1690_3 (m.d 0 2) (by simp) with h1716 | h1716
                          · linarith only [h1716, hlam, p1690_0]
                          · rcases p1690_3 (m.d 1 2) (by simp) with h1718 | h1718
                            · linarith only [h1678, h1718, hlam]
                            · rcases p1690_3 (m.d 2 3) (by simp) with h1720 | h1720
                              · rcases p1690_3 (m.d 2 4) (by simp) with h1721 | h1721
                                · rcases p1690_3 (m.d 2 5) (by simp) with h1722 | h1722
                                  · linarith only [h1687, h1722, hlam]
                                  · linarith only [h1381, h1722, hlam]
                                · linarith only [h1721, hlam, p1690_0]
                              · linarith only [h1720, h4, hlam]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          rcases p1690_3 (m.d 0 2) (by simp) with h1727 | h1727
                          · linarith only [h1290, h1727, hlam]
                          · linarith only [h0, h1727, hlam]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1685, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1436, h1682, h1687, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1690_1, u4ehi3]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          rcases p1690_3 (m.d 0 2) (by simp) with h1733 | h1733
                          · linarith only [h1733, hlam, p1690_0]
                          · rcases p1690_3 (m.d 1 2) (by simp) with h1735 | h1735
                            · linarith only [h1680, h1735, hlam]
                            · rcases p1690_3 (m.d 2 3) (by simp) with h1737 | h1737
                              · rcases p1690_3 (m.d 2 4) (by simp) with h1738 | h1738
                                · rcases p1690_3 (m.d 2 5) (by simp) with h1739 | h1739
                                  · rcases h4bigk with h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1436, h1682, hc45, hlam, hphi, p1740_1, u4ehi3]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1290, hlam, p1740_1]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1436, hc45, hlam, hphi, p1740_1, u4ehi3]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1436, hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h2, hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1678, hlam, p1740_1]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1740_1, u4ehi3]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1683, hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      rcases p1740_3 (m.d 0 4) (by simp) with h1751 | h1751
                                      · linarith only [h1290, h1751, hlam]
                                      · rcases p1740_3 (m.d 1 4) (by simp) with h1753 | h1753
                                        · linarith only [h1678, h1753, hlam]
                                        · rcases p1740_3 (m.d 2 4) (by simp) with h1755 | h1755
                                          · rcases p1740_3 (m.d 3 4) (by simp) with h1756 | h1756
                                            · linarith only [h1685, h1756, hlam]
                                            · rcases p1740_3 (m.d 4 5) (by simp) with h1758 | h1758
                                              · linarith only [h1687, h1758, hlam]
                                              · linarith only [h1436, h1758, hlam]
                                          · linarith only [h1290, h1755, hlam]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      rcases p1740_3 (m.d 0 4) (by simp) with h1762 | h1762
                                      · linarith only [h1290, h1762, hlam]
                                      · linarith only [h1762, h2, hlam]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      rcases p1740_3 (m.d 0 4) (by simp) with h1766 | h1766
                                      · linarith only [h1290, h1766, hlam]
                                      · linarith only [h1435, h1766, hlam]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1436, h1685, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1740_1, u4ehi0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1435, hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1682, hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1685, hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1688, hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [hc45, hlam, hphi, p1740_1, u4ehi0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [hc45, hlam, hphi, p1740_1, u4ehi1]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1687, hlam, p1740_0]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [h1685, h1687, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1740_1, u4ehi3]
                                    · have p1740_0 := h1740c.1
                                      have p1740_1 := h1740c.2.1
                                      have p1740_2 := h1740c.2.2.1
                                      have p1740_3 := h1740c.2.2.2
                                      linarith only [hlam, p1740_0]
                                  · linarith only [h1739, hlam, p1690_0]
                                · linarith only [h1290, h1738, hlam]
                              · linarith only [h1737, h4, hlam]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          rcases p1690_3 (m.d 0 2) (by simp) with h1783 | h1783
                          · linarith only [h1381, h1783, hlam]
                          · linarith only [h0, h1783, hlam]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1686, hlam, p1690_0]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [h1687, hlam, p1690_1]
                        · have p1690_0 := h1690c.1
                          have p1690_1 := h1690c.2.1
                          have p1690_2 := h1690c.2.2.1
                          have p1690_3 := h1690c.2.2.2
                          linarith only [hlam, p1690_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1789 | h1789
                      · linarith only [h0, h1, h1290, h1682, h1687, h1789, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h2bigk with h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1290, hc12, hc24, hlam, hphi, p1791_1]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h4, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1290, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1381, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h0, hlam, p1791_1]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1676, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1678, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1680, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          rcases p1791_3 (m.d 0 2) (by simp) with h1802 | h1802
                          · linarith only [h1802, hlam, p1791_0]
                          · rcases p1791_3 (m.d 1 2) (by simp) with h1804 | h1804
                            · linarith only [h1676, h1804, hlam]
                            · rcases p1791_3 (m.d 2 3) (by simp) with h1806 | h1806
                              · rcases p1791_3 (m.d 2 4) (by simp) with h1807 | h1807
                                · linarith only [h1685, h1807, hlam]
                                · linarith only [h1290, h1807, hlam]
                              · linarith only [h1806, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          rcases p1791_3 (m.d 0 2) (by simp) with h1811 | h1811
                          · linarith only [h1811, h4, hlam]
                          · linarith only [h0, h1811, hlam]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1290, hc02, hc23, hlam, hphi, p1791_1]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h0, h1381, hc12, hc23, hlam, hphi, p1791_1]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h0, h1687, hc12, hc45, hlam, hphi, ht23, ht34, p1791_1]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1687, hc12, hc45, hlam, hphi, ht23, ht34, p1791_1]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1685, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1687, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          rcases p1791_3 (m.d 0 2) (by simp) with h1822 | h1822
                          · linarith only [h1822, hlam, p1791_0]
                          · rcases p1791_3 (m.d 1 2) (by simp) with h1824 | h1824
                            · linarith only [h1680, h1824, hlam]
                            · rcases p1791_3 (m.d 2 3) (by simp) with h1826 | h1826
                              · rcases p1791_3 (m.d 2 4) (by simp) with h1827 | h1827
                                · linarith only [h1687, h1827, hlam]
                                · linarith only [h1290, h1827, hlam]
                              · linarith only [h1826, h4, hlam]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          rcases p1791_3 (m.d 0 2) (by simp) with h1831 | h1831
                          · linarith only [h1381, h1831, hlam]
                          · linarith only [h0, h1831, hlam]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h1686, hlam, p1791_0]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [h0, h1290, hc12, hc25, hlam, hphi, p1791_1]
                        · have p1791_0 := h1791c.1
                          have p1791_1 := h1791c.2.1
                          have p1791_2 := h1791c.2.2.1
                          have p1791_3 := h1791c.2.2.2
                          linarith only [hlam, p1791_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1837 | h1837
                    · linarith only [h1436, h1685, h1686, h1837, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1839 | h1839
                      · linarith only [h1682, h1837, h1839, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1, h1682, h1686, h1839, h4, hc45, hlam, hphi, u4ehi3]
                · linarith only [h1, h1682, h1685, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1843 | h1843
              · linarith only [h1436, h1843, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1845 | h1845
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1846 | h1846
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1847 | h1847
                    · linarith only [h1435, h1436, h1676, h1682, h1847, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1849 | h1849
                      · linarith only [h0, h1290, h1847, h1849, hc12, hc34, hlam, hphi, ht23]
                      · rcases h2bigk with h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p1851_1]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h4, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1290, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1381, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h0, hlam, p1851_1]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1676, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1678, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1680, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          rcases p1851_3 (m.d 0 2) (by simp) with h1862 | h1862
                          · linarith only [h1862, hlam, p1851_0]
                          · rcases p1851_3 (m.d 1 2) (by simp) with h1864 | h1864
                            · linarith only [h1676, h1864, hlam]
                            · rcases p1851_3 (m.d 2 3) (by simp) with h1866 | h1866
                              · rcases p1851_3 (m.d 2 4) (by simp) with h1867 | h1867
                                · linarith only [h1845, h1867, hlam]
                                · linarith only [h1290, h1867, hlam]
                              · linarith only [h1866, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          rcases p1851_3 (m.d 0 2) (by simp) with h1871 | h1871
                          · linarith only [h1871, h4, hlam]
                          · linarith only [h0, h1871, hlam]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1290, h1435, h1676, h1682, hc12, hc23, hlam, hphi, p1851_1]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1381, hc02, hc23, hlam, hphi, p1851_1]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h0, h1847, hc12, hc45, hlam, hphi, ht23, ht34, p1851_1]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1847, hc12, hc45, hlam, hphi, ht23, ht34, p1851_1]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1845, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1847, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          rcases p1851_3 (m.d 0 2) (by simp) with h1882 | h1882
                          · linarith only [h1882, hlam, p1851_0]
                          · rcases p1851_3 (m.d 1 2) (by simp) with h1884 | h1884
                            · linarith only [h1680, h1884, hlam]
                            · rcases p1851_3 (m.d 2 3) (by simp) with h1886 | h1886
                              · rcases p1851_3 (m.d 2 4) (by simp) with h1887 | h1887
                                · linarith only [h1847, h1887, hlam]
                                · linarith only [h1290, h1887, hlam]
                              · linarith only [h1886, h4, hlam]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          rcases p1851_3 (m.d 0 2) (by simp) with h1891 | h1891
                          · linarith only [h1381, h1891, hlam]
                          · linarith only [h0, h1891, hlam]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h1846, hlam, p1851_0]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [h0, h1290, hc12, hc25, hlam, hphi, p1851_1]
                        · have p1851_0 := h1851c.1
                          have p1851_1 := h1851c.2.1
                          have p1851_2 := h1851c.2.2.1
                          have p1851_3 := h1851c.2.2.2
                          linarith only [hlam, p1851_0]
                  · linarith only [h1435, h1676, h1682, h1846, h4, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1435, h1845, h4, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1899 | h1899
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1900 | h1900
      · linarith only [h0, h1900, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1902 | h1902
        · linarith only [h0, h1290, h1902, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1904 | h1904
          · linarith only [h0, h1381, h1904, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1906 | h1906
            · linarith only [h1, h1435, h1906, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1908 | h1908
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1909 | h1909
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1910 | h1910
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1911 | h1911
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1912 | h1912
                      · rcases h2bigk with h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c | h1913c
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1381, hc12, hc25, hlam, hphi, p1913_1]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h4, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1290, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1381, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h0, hlam, p1913_1]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1900, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1902, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1904, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          rcases p1913_3 (m.d 0 2) (by simp) with h1924 | h1924
                          · linarith only [h1924, hlam, p1913_0]
                          · rcases p1913_3 (m.d 1 2) (by simp) with h1926 | h1926
                            · linarith only [h1900, h1926, hlam]
                            · rcases p1913_3 (m.d 2 3) (by simp) with h1928 | h1928
                              · rcases p1913_3 (m.d 2 4) (by simp) with h1929 | h1929
                                · linarith only [h1909, h1929, hlam]
                                · linarith only [h1290, h1929, hlam]
                              · linarith only [h1928, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          rcases p1913_3 (m.d 0 2) (by simp) with h1933 | h1933
                          · linarith only [h1933, h4, hlam]
                          · linarith only [h0, h1933, hlam]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1435, h1909, h4, hc02, hc23, hlam, hphi, p1913_1]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h0, h1381, hc12, hc23, hlam, hphi, p1913_1]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          rcases p1913_3 (m.d 0 2) (by simp) with h1939 | h1939
                          · linarith only [h1939, hlam, p1913_0]
                          · rcases p1913_3 (m.d 1 2) (by simp) with h1941 | h1941
                            · linarith only [h1902, h1941, hlam]
                            · rcases p1913_3 (m.d 2 3) (by simp) with h1943 | h1943
                              · rcases p1913_3 (m.d 2 4) (by simp) with h1944 | h1944
                                · rcases p1913_3 (m.d 2 5) (by simp) with h1945 | h1945
                                  · linarith only [h1911, h1945, hlam]
                                  · linarith only [h1381, h1945, hlam]
                                · linarith only [h1944, hlam, p1913_0]
                              · linarith only [h1943, h4, hlam]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          rcases p1913_3 (m.d 0 2) (by simp) with h1950 | h1950
                          · linarith only [h1290, h1950, hlam]
                          · linarith only [h0, h1950, hlam]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1909, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h0, h1381, hc12, hc24, hlam, hphi, p1913_1]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          rcases p1913_3 (m.d 0 2) (by simp) with h1956 | h1956
                          · linarith only [h1956, hlam, p1913_0]
                          · rcases p1913_3 (m.d 1 2) (by simp) with h1958 | h1958
                            · linarith only [h1904, h1958, hlam]
                            · rcases p1913_3 (m.d 2 3) (by simp) with h1960 | h1960
                              · rcases p1913_3 (m.d 2 4) (by simp) with h1961 | h1961
                                · rcases p1913_3 (m.d 2 5) (by simp) with h1962 | h1962
                                  · rcases h4bigk with h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1908, hc04, hlam, hphi, ht0b, ht45, ht5b, p1963_1, u4ehi4]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1290, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1435, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1435, h1909, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1963_1, u4ehi4]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h2, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1902, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1906, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1963_1, u4ehi4]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1899, h1909, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1963_1, u4ehi4]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1908, h1909, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1963_1, u4ehi4]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h0, h1435, h1909, h4, hc12, hc23, hlam, hphi, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      rcases p1963_3 (m.d 0 4) (by simp) with h1978 | h1978
                                      · linarith only [h1290, h1978, hlam]
                                      · linarith only [h1899, h1978, hlam]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1908, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1963_1, u4ehi4]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1908, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1963_1, u4ehi4]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1909, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1909, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1963_1, u4ehi4]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1899, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1908, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1911, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1912, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                  · linarith only [h1962, hlam, p1913_0]
                                · linarith only [h1290, h1961, hlam]
                              · linarith only [h1960, h4, hlam]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          rcases p1913_3 (m.d 0 2) (by simp) with h1994 | h1994
                          · linarith only [h1381, h1994, hlam]
                          · linarith only [h0, h1994, hlam]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1910, hlam, p1913_0]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [h1911, hlam, p1913_1]
                        · have p1913_0 := h1913c.1
                          have p1913_1 := h1913c.2.1
                          have p1913_2 := h1913c.2.2.1
                          have p1913_3 := h1913c.2.2.2
                          linarith only [hlam, p1913_0]
                      · linarith only [h1908, h1912, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h1435, h1908, h1909, h1911, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h1435, h1908, h1909, h1910, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2003 | h2003
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2004 | h2004
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2005 | h2005
                      · rcases h2bigk with h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1381, hc12, hc25, hlam, hphi, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h4, hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1290, hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1381, hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h0, hlam, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1900, hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1902, hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1904, hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1909, hc02, hc34, hlam, hphi, ht23, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1909, hc12, hc34, hlam, hphi, ht23, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1909, hlam, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h0, h1381, hc12, hc23, hlam, hphi, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          rcases p2006_3 (m.d 0 2) (by simp) with h2022 | h2022
                          · linarith only [h2022, hlam, p2006_0]
                          · rcases p2006_3 (m.d 1 2) (by simp) with h2024 | h2024
                            · linarith only [h1902, h2024, hlam]
                            · rcases p2006_3 (m.d 2 3) (by simp) with h2026 | h2026
                              · linarith only [h1909, h2026, hlam]
                              · linarith only [h2026, h4, hlam]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          rcases p2006_3 (m.d 0 2) (by simp) with h2029 | h2029
                          · linarith only [h1290, h2029, hlam]
                          · linarith only [h0, h2029, hlam]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h0, h1909, h4, hc12, hc34, hlam, hphi, ht23, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h0, h1381, h1909, hc12, hc34, hlam, hphi, ht23, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h0, h1909, h2003, hc12, hc34, hlam, hphi, ht23, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h1909, h2003, hc12, hc34, hlam, hphi, ht23, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h2003, hlam, p2006_0]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [h2004, hlam, p2006_1]
                        · have p2006_0 := h2006c.1
                          have p2006_1 := h2006c.2.1
                          have p2006_2 := h2006c.2.2.1
                          have p2006_3 := h2006c.2.2.2
                          linarith only [hlam, p2006_0]
                      · linarith only [h1908, h1909, h2, h2005, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1290, h1899, h2004, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2042 | h2042
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2043 | h2043
                      · rcases h2bigk with h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c | h2044c
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h4, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1290, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1381, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h0, hlam, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1900, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1902, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1904, hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h2003, hc02, hc35, hlam, hphi, ht23, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h2003, hc12, hc35, hlam, hphi, ht23, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h1909, hlam, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h2003, hlam, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          rcases p2044_3 (m.d 0 2) (by simp) with h2060 | h2060
                          · linarith only [h2060, hlam, p2044_0]
                          · rcases p2044_3 (m.d 1 2) (by simp) with h2062 | h2062
                            · linarith only [h1902, h2062, hlam]
                            · rcases p2044_3 (m.d 2 3) (by simp) with h2064 | h2064
                              · linarith only [h1909, h2064, hlam]
                              · linarith only [h2064, h4, hlam]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          rcases p2044_3 (m.d 0 2) (by simp) with h2067 | h2067
                          · linarith only [h1290, h2067, hlam]
                          · linarith only [h0, h2067, hlam]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h0, h1909, h4, hc12, hc34, hlam, hphi, ht23, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h0, h1381, h1909, hc12, hc34, hlam, hphi, ht23, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          rcases p2044_3 (m.d 0 2) (by simp) with h2073 | h2073
                          · linarith only [h2073, hlam, p2044_0]
                          · rcases p2044_3 (m.d 1 2) (by simp) with h2075 | h2075
                            · linarith only [h1904, h2075, hlam]
                            · rcases p2044_3 (m.d 2 3) (by simp) with h2077 | h2077
                              · linarith only [h2003, h2077, hlam]
                              · linarith only [h2077, h4, hlam]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          rcases p2044_3 (m.d 0 2) (by simp) with h2080 | h2080
                          · linarith only [h1381, h2080, hlam]
                          · linarith only [h0, h2080, hlam]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h0, h4, hc12, hc25, hlam, hphi, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [h2042, hlam, p2044_1]
                        · have p2044_0 := h2044c.1
                          have p2044_1 := h2044c.2.1
                          have p2044_2 := h2044c.2.2.1
                          have p2044_3 := h2044c.2.2.2
                          linarith only [hlam, p2044_0]
                      · linarith only [h1290, h1908, h1909, h2, h2043, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h1290, h1908, h2, h2042, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2088 | h2088
                · linarith only [h1435, h1899, h1908, h2088, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2090 | h2090
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2091 | h2091
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2092 | h2092
                      · linarith only [h1908, h2088, h2090, h2092, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h2088, h2092, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1290, h1899, h2091, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2096 | h2096
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2097 | h2097
                      · rcases h2bigk with h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h2090, h2097, h4, hc12, hc34, hlam, hphi, ht23, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h4, hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h1290, hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h1381, hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h0, hlam, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h1900, hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h1902, hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h1904, hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h2090, h2097, hc02, hc34, hlam, hphi, ht23, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h2090, h2097, hc12, hc34, hlam, hphi, ht23, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h2088, hlam, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h2090, hlam, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          rcases p2098_3 (m.d 0 2) (by simp) with h2114 | h2114
                          · linarith only [h2114, hlam, p2098_0]
                          · rcases p2098_3 (m.d 1 2) (by simp) with h2116 | h2116
                            · linarith only [h1902, h2116, hlam]
                            · rcases p2098_3 (m.d 2 3) (by simp) with h2118 | h2118
                              · linarith only [h2088, h2118, hlam]
                              · linarith only [h2118, h4, hlam]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          rcases p2098_3 (m.d 0 2) (by simp) with h2121 | h2121
                          · linarith only [h1290, h2121, hlam]
                          · linarith only [h0, h2121, hlam]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h0, h4, hc12, hc24, hlam, hphi, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [hlam, p2098_0]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h1381, h1899, h1908, h2088, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2098_1, u4ehi1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          rcases p2098_3 (m.d 0 2) (by simp) with h2127 | h2127
                          · linarith only [h2127, hlam, p2098_0]
                          · rcases p2098_3 (m.d 1 2) (by simp) with h2129 | h2129
                            · linarith only [h1904, h2129, hlam]
                            · rcases p2098_3 (m.d 2 3) (by simp) with h2131 | h2131
                              · linarith only [h2090, h2131, hlam]
                              · linarith only [h2131, h4, hlam]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          rcases p2098_3 (m.d 0 2) (by simp) with h2134 | h2134
                          · linarith only [h1381, h2134, hlam]
                          · linarith only [h0, h2134, hlam]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h0, h4, hc12, hc25, hlam, hphi, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [h2096, hlam, p2098_1]
                        · have p2098_0 := h2098c.1
                          have p2098_1 := h2098c.2.1
                          have p2098_2 := h2098c.2.2.1
                          have p2098_3 := h2098c.2.2.2
                          linarith only [hlam, p2098_0]
                      · linarith only [h1290, h1899, h2088, h2097, hlam]
                    · linarith only [h1290, h1899, h2096, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2142 | h2142
      · linarith only [h0, h2142, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2144 | h2144
        · linarith only [h0, h1290, h2144, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2146 | h2146
          · linarith only [h0, h1381, h2146, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2148 | h2148
            · linarith only [h1, h1435, h1899, h2148, hc45, hlam, hphi, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2150 | h2150
              · linarith only [h1899, h2, h2150, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2152 | h2152
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2153 | h2153
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2154 | h2154
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2155 | h2155
                      · linarith only [h1899, h2152, h2155, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h0, h1435, h2152, h2154, h2155, h4, hc12, hc23, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2158 | h2158
                      · linarith only [h0, h1290, h2154, h2158, hc12, hc34, hlam, hphi, ht23]
                      · rcases h2bigk with h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h1435, h2152, h4, hc12, hc24, hlam, hphi, p2160_1]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h4, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h1290, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h1381, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h0, hlam, p2160_1]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h2142, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h2144, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h2146, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          rcases p2160_3 (m.d 0 2) (by simp) with h2171 | h2171
                          · linarith only [h2171, hlam, p2160_0]
                          · rcases p2160_3 (m.d 1 2) (by simp) with h2173 | h2173
                            · linarith only [h2142, h2173, hlam]
                            · rcases p2160_3 (m.d 2 3) (by simp) with h2175 | h2175
                              · rcases p2160_3 (m.d 2 4) (by simp) with h2176 | h2176
                                · linarith only [h2152, h2176, hlam]
                                · linarith only [h1290, h2176, hlam]
                              · linarith only [h2175, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          rcases p2160_3 (m.d 0 2) (by simp) with h2180 | h2180
                          · linarith only [h2180, h4, hlam]
                          · linarith only [h0, h2180, hlam]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h1435, h2152, h4, hc02, hc23, hlam, hphi, p2160_1]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h0, h1381, hc12, hc23, hlam, hphi, p2160_1]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h0, h2154, hc12, hc45, hlam, hphi, ht23, ht34, p2160_1]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h2154, hc12, hc45, hlam, hphi, ht23, ht34, p2160_1]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h2152, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h2154, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          rcases p2160_3 (m.d 0 2) (by simp) with h2191 | h2191
                          · linarith only [h2191, hlam, p2160_0]
                          · rcases p2160_3 (m.d 1 2) (by simp) with h2193 | h2193
                            · linarith only [h2146, h2193, hlam]
                            · rcases p2160_3 (m.d 2 3) (by simp) with h2195 | h2195
                              · rcases p2160_3 (m.d 2 4) (by simp) with h2196 | h2196
                                · linarith only [h2154, h2196, hlam]
                                · linarith only [h1290, h2196, hlam]
                              · linarith only [h2195, h4, hlam]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          rcases p2160_3 (m.d 0 2) (by simp) with h2200 | h2200
                          · linarith only [h1381, h2200, hlam]
                          · linarith only [h0, h2200, hlam]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h2153, hlam, p2160_0]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [h0, h1290, hc12, hc25, hlam, hphi, p2160_1]
                        · have p2160_0 := h2160c.1
                          have p2160_1 := h2160c.2.1
                          have p2160_2 := h2160c.2.2.1
                          have p2160_3 := h2160c.2.2.2
                          linarith only [hlam, p2160_0]
                  · linarith only [h0, h1435, h2152, h2153, h4, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2207 | h2207
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2208 | h2208
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2209 | h2209
                      · linarith only [h1899, h2, h2152, h2207, h2209, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                      · linarith only [h2152, h2207, h2208, h2209, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h2152, h2207, h2208, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2213 | h2213
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2214 | h2214
                      · rcases h2bigk with h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c | h2215c
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h4, hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h1290, hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h1381, hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h0, hlam, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h2142, hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h2144, hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h2146, hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h2207, hc02, hc35, hlam, hphi, ht23, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h2207, hc12, hc35, hlam, hphi, ht23, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h2152, hlam, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h2207, hlam, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          rcases p2215_3 (m.d 0 2) (by simp) with h2231 | h2231
                          · linarith only [h2231, hlam, p2215_0]
                          · rcases p2215_3 (m.d 1 2) (by simp) with h2233 | h2233
                            · linarith only [h2144, h2233, hlam]
                            · rcases p2215_3 (m.d 2 3) (by simp) with h2235 | h2235
                              · linarith only [h2152, h2235, hlam]
                              · linarith only [h2235, h4, hlam]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          rcases p2215_3 (m.d 0 2) (by simp) with h2238 | h2238
                          · linarith only [h1290, h2238, hlam]
                          · linarith only [h0, h2238, hlam]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h0, h4, hc12, hc24, hlam, hphi, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [hlam, p2215_0]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h0, h2152, h2207, h4, hc12, hc34, hlam, hphi, ht23, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          rcases p2215_3 (m.d 0 2) (by simp) with h2244 | h2244
                          · linarith only [h2244, hlam, p2215_0]
                          · rcases p2215_3 (m.d 1 2) (by simp) with h2246 | h2246
                            · linarith only [h2146, h2246, hlam]
                            · rcases p2215_3 (m.d 2 3) (by simp) with h2248 | h2248
                              · linarith only [h2207, h2248, hlam]
                              · linarith only [h2248, h4, hlam]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          rcases p2215_3 (m.d 0 2) (by simp) with h2251 | h2251
                          · linarith only [h1381, h2251, hlam]
                          · linarith only [h0, h2251, hlam]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h0, h4, hc12, hc25, hlam, hphi, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [h2213, hlam, p2215_1]
                        · have p2215_0 := h2215c.1
                          have p2215_1 := h2215c.2.1
                          have p2215_2 := h2215c.2.2.1
                          have p2215_3 := h2215c.2.2.2
                          linarith only [hlam, p2215_0]
                      · linarith only [h0, h2152, h2214, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2258 | h2258
                      · linarith only [h0, h1290, h2213, h2258, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2152, h2258, h4, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
