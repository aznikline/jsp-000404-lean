import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_61S0
import Jsp000404.R1LeavesN7_61S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h460 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h563 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h632 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1432 | h1432
  · linarith only [h1432, h632, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1434 | h1434
    · linarith only [h1434, h632, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1436 | h1436
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1437 | h1437
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1438 | h1438
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1439 | h1439
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1440 | h1440
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1441 | h1441
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1442 | h1442
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1443 | h1443
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1444 | h1444
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1445 | h1445
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1446 | h1446
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1447 | h1447
                            · linarith only [h1436, h1439, h1447, h632, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h1432, h1438, h1439, h1444, h1447, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1432, h1438, h1446, hlam]
                        · linarith only [h1445, h632, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1444, h632, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1438, h1443, h460, hlam]
                  · linarith only [h1436, h1439, h1442, h632, hlam]
                · linarith only [h1439, h1441, h632, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1439, h1440, h632, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1457 | h1457
              · linarith only [h1439, h1457, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1459 | h1459
                · linarith only [h1439, h1459, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1461 | h1461
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1462 | h1462
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1463 | h1463
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1464 | h1464
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1465 | h1465
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1466 | h1466
                            · rcases h0bigk with h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c | h1467c
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h0, hlam, p1467_1]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h328, hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h460, hlam, p1467_1]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h563, hlam, p1467_1]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h0, h1459, h1463, h1465, hc01, hc23, hlam, hphi, ht12, p1467_1]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h632, hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1432, hlam, p1467_1]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1434, hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                rcases p1467_3 (m.d 0 1) (by simp) with h1478 | h1478
                                · linarith only [h1478, h328, hlam]
                                · rcases p1467_3 (m.d 0 2) (by simp) with h1480 | h1480
                                  · linarith only [h1480, h632, hlam]
                                  · linarith only [h0, h1480, hlam]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1439, h328, hc23, hlam, hphi, p1467_1, u2ehi0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1432, h1439, h328, hc23, hlam, hphi, p1467_1, u2ehi0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1434, h1439, h328, hc23, hlam, hphi, p1467_1, u2ehi0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                rcases p1467_3 (m.d 0 1) (by simp) with h1487 | h1487
                                · linarith only [h1487, h460, hlam]
                                · rcases p1467_3 (m.d 0 2) (by simp) with h1489 | h1489
                                  · linarith only [h1432, h1489, hlam]
                                  · linarith only [h0, h1489, hlam]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1432, h1463, hc23, hlam, hphi, p1467_1, u2ehi0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1436, hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1434, h1436, h1439, h328, hc23, hlam, hphi, p1467_1, u2ehi0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                rcases p1467_3 (m.d 0 1) (by simp) with h1496 | h1496
                                · linarith only [h1496, h563, hlam]
                                · rcases p1467_3 (m.d 0 2) (by simp) with h1498 | h1498
                                  · linarith only [h1434, h1498, hlam]
                                  · linarith only [h0, h1498, hlam]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1434, h1463, h1465, hc23, hlam, hphi, p1467_1, u2ehi0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1437, hlam, p1467_0]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [h1438, hlam, p1467_1]
                              · have p1467_0 := h1467c.1
                                have p1467_1 := h1467c.2.1
                                have p1467_2 := h1467c.2.2.1
                                have p1467_3 := h1467c.2.2.2
                                linarith only [hlam, p1467_0]
                            · rcases h0bigk with h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h0, hlam, p1505_1]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h328, hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h460, hlam, p1505_1]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h563, hlam, p1505_1]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h0, h1459, h1463, h1465, hc01, hc23, hlam, hphi, ht12, p1505_1]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h632, hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1432, hlam, p1505_1]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1434, hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                rcases p1505_3 (m.d 0 1) (by simp) with h1516 | h1516
                                · linarith only [h1516, h328, hlam]
                                · rcases p1505_3 (m.d 0 2) (by simp) with h1518 | h1518
                                  · linarith only [h1518, h632, hlam]
                                  · linarith only [h0, h1518, hlam]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1439, h328, hc23, hlam, hphi, p1505_1, u2ehi0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1438, h1439, h1466, h328, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1505_1]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1434, h1439, h328, hc23, hlam, hphi, p1505_1, u2ehi0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                rcases p1505_3 (m.d 0 1) (by simp) with h1525 | h1525
                                · linarith only [h1525, h460, hlam]
                                · rcases p1505_3 (m.d 0 2) (by simp) with h1527 | h1527
                                  · linarith only [h1432, h1527, hlam]
                                  · linarith only [h0, h1527, hlam]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1432, h1463, hc23, hlam, hphi, p1505_1, u2ehi0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1436, hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1436, h1438, h1439, h1466, h328, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1505_1, u3ehi3]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                rcases p1505_3 (m.d 0 1) (by simp) with h1534 | h1534
                                · linarith only [h1534, h563, hlam]
                                · rcases p1505_3 (m.d 0 2) (by simp) with h1536 | h1536
                                  · linarith only [h1434, h1536, hlam]
                                  · linarith only [h0, h1536, hlam]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1434, h1463, h1465, hc23, hlam, hphi, p1505_1, u2ehi0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1437, hlam, p1505_0]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [h1438, hlam, p1505_1]
                              · have p1505_0 := h1505c.1
                                have p1505_1 := h1505c.2.1
                                have p1505_2 := h1505c.2.2.1
                                have p1505_3 := h1505c.2.2.2
                                linarith only [hlam, p1505_0]
                          · linarith only [h1432, h1465, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1436, h1439, h1464, h328, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1436, h1439, h1463, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h1436, h1438, h1439, h1462, h328, h460, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1436, h1461, h328, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1548 | h1548
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1549 | h1549
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1550 | h1550
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1551 | h1551
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1552 | h1552
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1553 | h1553
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1554 | h1554
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1555 | h1555
                          · linarith only [h1432, h1438, h1548, h1553, h1555, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1432, h1555, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1437, h1554, h632, hlam]
                      · linarith only [h1437, h1553, h632, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1432, h1549, h1552, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h1436, h1551, h328, hlam]
                · linarith only [h1548, h1550, h632, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1548, h1549, h632, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1564 | h1564
              · linarith only [h1548, h1564, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1566 | h1566
                · linarith only [h1548, h1566, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1568 | h1568
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1569 | h1569
                    · linarith only [h1432, h1438, h1564, h1569, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1571 | h1571
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1572 | h1572
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1573 | h1573
                          · linarith only [h1432, h1569, h1571, h1573, h460, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1432, h1573, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1572, h632, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1436, h1548, h1571, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · linarith only [h1436, h1438, h1568, h328, hc45, hlam, hphi, ht34, u3ehi0]
        · linarith only [h1436, h1437, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1580 | h1580
        · linarith only [h1436, h1580, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1582 | h1582
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1583 | h1583
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1584 | h1584
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1585 | h1585
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1586 | h1586
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1587 | h1587
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1588 | h1588
                      · linarith only [h1436, h1582, h1583, h1588, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h1588, h632, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1582, h1587, h460, hlam]
                  · linarith only [h1583, h1586, h632, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1432, h1582, h1584, h1585, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · linarith only [h1583, h1584, h632, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1595 | h1595
              · linarith only [h1583, h1595, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1597 | h1597
                · linarith only [h1583, h1597, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1599 | h1599
                  · linarith only [h1436, h1583, h1599, h632, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1601 | h1601
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1602 | h1602
                      · linarith only [h1583, h1599, h1602, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1602, h632, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1582, h1601, h460, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1606 | h1606
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1607 | h1607
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1608 | h1608
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1609 | h1609
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1610 | h1610
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1611 | h1611
                      · linarith only [h1436, h1606, h1611, h632, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1611, h632, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1432, h1607, h1610, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h1606, h1609, h632, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1606, h1608, h632, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1606, h1607, h632, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1618 | h1618
              · linarith only [h1606, h1618, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1620 | h1620
                · linarith only [h1606, h1620, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1622 | h1622
                  · linarith only [h1436, h1606, h1622, h632, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1624 | h1624
                    · linarith only [h1432, h1582, h1618, h1624, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1626 | h1626
                      · linarith only [h1436, h1626, h632, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h1626, h632, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h460 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h563 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h632 | h632
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h328 h460 h563 h632
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h328 h460 h563 h632

set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h460 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h563 | h563
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h328 h460 h563
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h328 h460 h563

set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h460 | h460
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h328 h460
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h328 h460

set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h328 | h328
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x0 m hb0 hb2 hb3 hb5 h0 h328
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1 m hb0 hb2 hb3 hb5 h0 h328

set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
