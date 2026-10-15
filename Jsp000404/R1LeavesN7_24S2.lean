import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h1435 | h1435
  · linarith only [h1435, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1437 | h1437
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1438 | h1438
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1439 | h1439
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1440 | h1440
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1441 | h1441
            · linarith only [h1441, h8, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1443 | h1443
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1444 | h1444
                · linarith only [h1, h1437, h1444, h8, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1446 | h1446
                  · linarith only [h1435, h1438, h1446, h2, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1448 | h1448
                    · linarith only [h1, h1435, h1437, h1443, h1448, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · rcases h0bigk with h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c | h1450c
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h0, h1439, h1443, h1444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1450_1]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        rcases p1450_3 (m.d 0 1) (by simp) with h1453 | h1453
                        · rcases p1450_3 (m.d 0 2) (by simp) with h1454 | h1454
                          · linarith only [h0, h1454, hlam]
                          · linarith only [h1454, h4, hlam]
                        · linarith only [h1, h1453, hlam]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        rcases p1450_3 (m.d 0 1) (by simp) with h1458 | h1458
                        · rcases p1450_3 (m.d 0 2) (by simp) with h1459 | h1459
                          · linarith only [h0, h1459, hlam]
                          · linarith only [h1459, h5, hlam]
                        · linarith only [h1458, h2, hlam]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        rcases p1450_3 (m.d 0 1) (by simp) with h1463 | h1463
                        · rcases p1450_3 (m.d 0 2) (by simp) with h1464 | h1464
                          · linarith only [h0, h1464, hlam]
                          · linarith only [h1464, h6, hlam]
                        · linarith only [h1463, h3, hlam]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h0, hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        rcases p1450_3 (m.d 0 1) (by simp) with h1470 | h1470
                        · rcases p1450_3 (m.d 0 2) (by simp) with h1471 | h1471
                          · rcases p1450_3 (m.d 0 3) (by simp) with h1472 | h1472
                            · linarith only [h1472, h4, hlam]
                            · rcases p1450_3 (m.d 0 4) (by simp) with h1474 | h1474
                              · linarith only [h1474, h5, hlam]
                              · rcases p1450_3 (m.d 0 5) (by simp) with h1476 | h1476
                                · linarith only [h1476, h6, hlam]
                                · linarith only [h1476, h8, hlam]
                          · linarith only [h1471, h4, hlam]
                        · linarith only [h1, h1470, hlam]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        rcases p1450_3 (m.d 0 1) (by simp) with h1481 | h1481
                        · rcases p1450_3 (m.d 0 2) (by simp) with h1482 | h1482
                          · rcases p1450_3 (m.d 0 3) (by simp) with h1483 | h1483
                            · linarith only [h1483, h4, hlam]
                            · linarith only [h1483, h7, hlam]
                          · linarith only [h1482, h5, hlam]
                        · linarith only [h1481, h2, hlam]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        rcases p1450_3 (m.d 0 1) (by simp) with h1488 | h1488
                        · rcases p1450_3 (m.d 0 2) (by simp) with h1489 | h1489
                          · rcases p1450_3 (m.d 0 3) (by simp) with h1490 | h1490
                            · linarith only [h1490, h4, hlam]
                            · rcases p1450_3 (m.d 0 4) (by simp) with h1492 | h1492
                              · linarith only [h1492, h5, hlam]
                              · rcases p1450_3 (m.d 0 5) (by simp) with h1494 | h1494
                                · linarith only [h1494, h6, hlam]
                                · rcases h0emin with h1496 | h1496 | h1496 | h1496 | h1496
                                  · rcases h2bigk with h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h0, h1439, h1443, h1444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1497_1]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      rcases p1497_3 (m.d 0 2) (by simp) with h1500 | h1500
                                      · rcases p1497_3 (m.d 1 2) (by simp) with h1501 | h1501
                                        · linarith only [h0, h1501, hlam]
                                        · linarith only [h1437, h1501, hlam]
                                      · linarith only [h1500, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      rcases p1497_3 (m.d 0 2) (by simp) with h1505 | h1505
                                      · rcases p1497_3 (m.d 1 2) (by simp) with h1506 | h1506
                                        · linarith only [h0, h1506, hlam]
                                        · linarith only [h1438, h1506, hlam]
                                      · linarith only [h1505, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      rcases p1497_3 (m.d 0 2) (by simp) with h1510 | h1510
                                      · rcases p1497_3 (m.d 1 2) (by simp) with h1511 | h1511
                                        · linarith only [h0, h1511, hlam]
                                        · linarith only [h1439, h1511, hlam]
                                      · linarith only [h1510, hlam, p1497_0]
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
                                      linarith only [h0, h1443, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1497_1]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      rcases p1497_3 (m.d 0 2) (by simp) with h1518 | h1518
                                      · rcases p1497_3 (m.d 1 2) (by simp) with h1519 | h1519
                                        · rcases p1497_3 (m.d 2 3) (by simp) with h1520 | h1520
                                          · linarith only [h1437, h1520, hlam]
                                          · linarith only [h1443, h1520, hlam]
                                        · linarith only [h1519, hlam, p1497_0]
                                      · linarith only [h1518, h5, hlam]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h0, h1443, h1444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1497_1]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h4, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h1437, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h4, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1497_1, u3elo4]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h1444, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h5, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h1438, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h1443, hlam, p1497_1]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h1446, hlam, p1497_1]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h6, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h1439, hlam, p1497_0]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1450_1, p1497_1]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [h0, h1439, h1443, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1450_1, p1497_1]
                                    · have p1497_0 := h1497c.1
                                      have p1497_1 := h1497c.2.1
                                      have p1497_2 := h1497c.2.2.1
                                      have p1497_3 := h1497c.2.2.2
                                      linarith only [hlam, p1497_0]
                                  · rcases h2bigk with h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h0, h1437, h1443, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1541_1]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      rcases p1541_3 (m.d 0 2) (by simp) with h1544 | h1544
                                      · rcases p1541_3 (m.d 1 2) (by simp) with h1545 | h1545
                                        · linarith only [h0, h1545, hlam]
                                        · linarith only [h1437, h1545, hlam]
                                      · linarith only [h1544, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      rcases p1541_3 (m.d 0 2) (by simp) with h1549 | h1549
                                      · rcases p1541_3 (m.d 1 2) (by simp) with h1550 | h1550
                                        · linarith only [h0, h1550, hlam]
                                        · linarith only [h1438, h1550, hlam]
                                      · linarith only [h1549, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      rcases p1541_3 (m.d 0 2) (by simp) with h1554 | h1554
                                      · rcases p1541_3 (m.d 1 2) (by simp) with h1555 | h1555
                                        · linarith only [h0, h1555, hlam]
                                        · linarith only [h1439, h1555, hlam]
                                      · linarith only [h1554, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h0, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h0, h1443, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1541_1]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      rcases p1541_3 (m.d 0 2) (by simp) with h1562 | h1562
                                      · rcases p1541_3 (m.d 1 2) (by simp) with h1563 | h1563
                                        · rcases p1541_3 (m.d 2 3) (by simp) with h1564 | h1564
                                          · linarith only [h1437, h1564, hlam]
                                          · linarith only [h1443, h1564, hlam]
                                        · linarith only [h1563, hlam, p1541_0]
                                      · linarith only [h1562, h5, hlam]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h0, h1443, h1444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1541_1]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h4, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h1437, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h1, h1437, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1541_1, u3elo4]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h1444, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h5, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h1438, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h1443, hlam, p1541_1]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h1446, hlam, p1541_1]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h6, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h1439, hlam, p1541_0]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1450_1, p1541_1]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [h0, h1439, h1443, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1450_1, p1541_1]
                                    · have p1541_0 := h1541c.1
                                      have p1541_1 := h1541c.2.1
                                      have p1541_2 := h1541c.2.2.1
                                      have p1541_3 := h1541c.2.2.2
                                      linarith only [hlam, p1541_0]
                                  · linarith only [h1496, h8, hlam, ht01, ht12, ht23, u3elo4]
                                  · linarith only [h1496, h7, h8, hlam, ht01, ht12, ht23, u3elo4]
                                  · linarith only [h0, h1496, hc01, hlam, p1450_1]
                          · linarith only [h1489, h6, hlam]
                        · linarith only [h1488, h3, hlam]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h1, hlam, p1450_1]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h4, hlam, p1450_1]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1450_1, u3elo4]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h8, hlam, p1450_1]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h2, hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h5, hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h7, hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h1435, hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h3, hlam, p1450_0]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h6, hlam, p1450_1]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [h1, h1437, h1443, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1450_1, u3elo4]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        rcases p1450_3 (m.d 0 1) (by simp) with h1603 | h1603
                        · rcases p1450_3 (m.d 0 2) (by simp) with h1604 | h1604
                          · rcases p1450_3 (m.d 0 3) (by simp) with h1605 | h1605
                            · linarith only [h1605, h8, hlam]
                            · linarith only [h1605, h7, hlam]
                          · linarith only [h1604, h5, hlam]
                        · linarith only [h1603, h2, hlam]
                      · have p1450_0 := h1450c.1
                        have p1450_1 := h1450c.2.1
                        have p1450_2 := h1450c.2.2.1
                        have p1450_3 := h1450c.2.2.2
                        linarith only [hlam, p1450_0]
              · linarith only [h1443, h7, hc23, hlam, hphi, u3elo0]
          · linarith only [h1440, h7, h8, hc13, hlam, hphi, u3elo4]
        · linarith only [h1437, h1439, h6, h8, hc23, hlam, hphi, u3elo4]
      · linarith only [h1437, h1438, h5, h7, h8, hc23, hlam, hphi, u3elo4]
    · linarith only [h1437, h4, h8, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1616 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h1617 | h1617
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1618 | h1618
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1619 | h1619
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1620 | h1620
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1621 | h1621
          · linarith only [h1, h1621, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1623 | h1623
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1624 | h1624
              · linarith only [h1, h1618, h1624, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1626 | h1626
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1627 | h1627
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1628 | h1628
                    · rcases h0bigk with h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h0, h1619, h1624, h1626, hc01, hc35, hlam, hphi, ht0b, ht5b, p1629_1]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        rcases p1629_3 (m.d 0 1) (by simp) with h1632 | h1632
                        · rcases p1629_3 (m.d 0 2) (by simp) with h1633 | h1633
                          · linarith only [h0, h1633, hlam]
                          · linarith only [h1633, h4, hlam]
                        · linarith only [h1, h1632, hlam]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        rcases p1629_3 (m.d 0 1) (by simp) with h1637 | h1637
                        · rcases p1629_3 (m.d 0 2) (by simp) with h1638 | h1638
                          · linarith only [h0, h1638, hlam]
                          · linarith only [h1638, h5, hlam]
                        · linarith only [h1637, h2, hlam]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        rcases p1629_3 (m.d 0 1) (by simp) with h1642 | h1642
                        · rcases p1629_3 (m.d 0 2) (by simp) with h1643 | h1643
                          · linarith only [h0, h1643, hlam]
                          · linarith only [h1643, h6, hlam]
                        · linarith only [h1642, h3, hlam]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h0, hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        rcases p1629_3 (m.d 0 1) (by simp) with h1649 | h1649
                        · rcases p1629_3 (m.d 0 2) (by simp) with h1650 | h1650
                          · rcases p1629_3 (m.d 0 3) (by simp) with h1651 | h1651
                            · linarith only [h1651, h4, hlam]
                            · rcases p1629_3 (m.d 0 4) (by simp) with h1653 | h1653
                              · linarith only [h1653, h5, hlam]
                              · linarith only [h1653, h7, hlam]
                          · linarith only [h1650, h4, hlam]
                        · linarith only [h1, h1649, hlam]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        rcases p1629_3 (m.d 0 1) (by simp) with h1658 | h1658
                        · rcases p1629_3 (m.d 0 2) (by simp) with h1659 | h1659
                          · rcases p1629_3 (m.d 0 3) (by simp) with h1660 | h1660
                            · linarith only [h1660, h4, hlam]
                            · rcases p1629_3 (m.d 0 4) (by simp) with h1662 | h1662
                              · linarith only [h1662, h5, hlam]
                              · rcases p1629_3 (m.d 0 5) (by simp) with h1664 | h1664
                                · linarith only [h1664, h6, hlam]
                                · rcases h0emin with h1666 | h1666 | h1666 | h1666 | h1666
                                  · rcases h2bigk with h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h1619, h1624, h1626, h1628, hc02, hc45, hlam, hphi, ht0b, ht5b, p1667_1]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      rcases p1667_3 (m.d 0 2) (by simp) with h1670 | h1670
                                      · rcases p1667_3 (m.d 1 2) (by simp) with h1671 | h1671
                                        · linarith only [h0, h1671, hlam]
                                        · linarith only [h1618, h1671, hlam]
                                      · linarith only [h1670, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      rcases p1667_3 (m.d 0 2) (by simp) with h1675 | h1675
                                      · rcases p1667_3 (m.d 1 2) (by simp) with h1676 | h1676
                                        · linarith only [h0, h1676, hlam]
                                        · linarith only [h1619, h1676, hlam]
                                      · linarith only [h1675, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      rcases p1667_3 (m.d 0 2) (by simp) with h1680 | h1680
                                      · rcases p1667_3 (m.d 1 2) (by simp) with h1681 | h1681
                                        · linarith only [h0, h1681, hlam]
                                        · linarith only [h1620, h1681, hlam]
                                      · linarith only [h1680, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h0, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h0, h1626, h1628, hc01, hc45, hlam, hphi, ht0b, ht5b, p1667_1]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h0, h1624, h1626, h1628, hc01, hc45, hlam, hphi, ht0b, ht5b, p1667_1]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      rcases p1667_3 (m.d 0 2) (by simp) with h1689 | h1689
                                      · rcases p1667_3 (m.d 1 2) (by simp) with h1690 | h1690
                                        · rcases p1667_3 (m.d 2 3) (by simp) with h1691 | h1691
                                          · linarith only [h1618, h1691, hlam]
                                          · linarith only [h1626, h1691, hlam]
                                        · linarith only [h1690, hlam, p1667_0]
                                      · linarith only [h1689, h6, hlam]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h4, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h1618, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h1624, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h1, h1618, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1667_1, u3elo3]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h5, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h1619, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h0, h1626, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p1667_1]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h0, h1619, h1626, h1628, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1629_1, p1667_1]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h6, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h1620, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h1626, hlam, p1667_1]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [h1627, hlam, p1667_0]
                                    · have p1667_0 := h1667c.1
                                      have p1667_1 := h1667c.2.1
                                      have p1667_2 := h1667c.2.2.1
                                      have p1667_3 := h1667c.2.2.2
                                      linarith only [hlam, p1667_0]
                                  · rcases h2bigk with h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c | h1711c
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h0, h1618, h1626, h1628, hc01, hc45, hlam, hphi, ht0b, ht5b, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      rcases p1711_3 (m.d 0 2) (by simp) with h1714 | h1714
                                      · rcases p1711_3 (m.d 1 2) (by simp) with h1715 | h1715
                                        · linarith only [h0, h1715, hlam]
                                        · linarith only [h1618, h1715, hlam]
                                      · linarith only [h1714, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      rcases p1711_3 (m.d 0 2) (by simp) with h1719 | h1719
                                      · rcases p1711_3 (m.d 1 2) (by simp) with h1720 | h1720
                                        · linarith only [h0, h1720, hlam]
                                        · linarith only [h1619, h1720, hlam]
                                      · linarith only [h1719, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      rcases p1711_3 (m.d 0 2) (by simp) with h1724 | h1724
                                      · rcases p1711_3 (m.d 1 2) (by simp) with h1725 | h1725
                                        · linarith only [h0, h1725, hlam]
                                        · linarith only [h1620, h1725, hlam]
                                      · linarith only [h1724, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h0, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h0, h1626, h1628, hc01, hc45, hlam, hphi, ht0b, ht5b, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h0, h1624, h1626, h1628, hc01, hc45, hlam, hphi, ht0b, ht5b, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      rcases p1711_3 (m.d 0 2) (by simp) with h1733 | h1733
                                      · rcases p1711_3 (m.d 1 2) (by simp) with h1734 | h1734
                                        · rcases p1711_3 (m.d 2 3) (by simp) with h1735 | h1735
                                          · linarith only [h1618, h1735, hlam]
                                          · linarith only [h1626, h1735, hlam]
                                        · linarith only [h1734, hlam, p1711_0]
                                      · linarith only [h1733, h6, hlam]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h4, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1618, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1624, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h4, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1711_1, u3elo3]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h5, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1619, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h0, h1619, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1629_1, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h0, h1619, h1626, h1628, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1629_1, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h6, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1620, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1626, hlam, p1711_1]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [h1627, hlam, p1711_0]
                                    · have p1711_0 := h1711c.1
                                      have p1711_1 := h1711c.2.1
                                      have p1711_2 := h1711c.2.2.1
                                      have p1711_3 := h1711c.2.2.2
                                      linarith only [hlam, p1711_0]
                                  · linarith only [h1666, h7, hlam, ht01, ht12, ht23, u3elo3]
                                  · linarith only [h0, h1666, hc01, hlam, p1629_1]
                                  · linarith only [h1616, h1666, h7, hlam, ht01, ht12, ht23, u3elo3]
                          · linarith only [h1659, h5, hlam]
                        · linarith only [h1658, h2, hlam]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        rcases p1629_3 (m.d 0 1) (by simp) with h1760 | h1760
                        · rcases p1629_3 (m.d 0 2) (by simp) with h1761 | h1761
                          · rcases p1629_3 (m.d 0 3) (by simp) with h1762 | h1762
                            · linarith only [h1762, h4, hlam]
                            · linarith only [h1616, h1762, hlam]
                          · linarith only [h1761, h6, hlam]
                        · linarith only [h1760, h3, hlam]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h1, hlam, p1629_1]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h4, hlam, p1629_1]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h7, hlam, p1629_1]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1629_1, u3elo3]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h2, hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h5, hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h7, hc03, hlam, hphi, p1629_1, u3elo3]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        rcases p1629_3 (m.d 0 1) (by simp) with h1776 | h1776
                        · rcases p1629_3 (m.d 0 2) (by simp) with h1777 | h1777
                          · rcases p1629_3 (m.d 0 3) (by simp) with h1778 | h1778
                            · linarith only [h1778, h7, hlam]
                            · linarith only [h1616, h1778, hlam]
                          · linarith only [h1777, h6, hlam]
                        · linarith only [h1776, h3, hlam]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h3, hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h6, hlam, p1629_1]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h1616, hlam, p1629_0]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [h1617, hlam, p1629_1]
                      · have p1629_0 := h1629c.1
                        have p1629_1 := h1629c.2.1
                        have p1629_2 := h1629c.2.2.1
                        have p1629_3 := h1629c.2.2.2
                        linarith only [hlam, p1629_0]
                    · linarith only [h1617, h1628, h7, hlam]
                  · linarith only [h1616, h1617, h1624, h1627, h7, hc23, hlam, hphi, u3elo3]
                · linarith only [h1623, h1626, hc23, hlam, hphi, u3elo1]
            · linarith only [h1616, h1623, h7, hc13, hlam, hphi, u3elo3]
        · linarith only [h1616, h1620, h6, h7, hc12, hlam, hphi, ht23, u3elo3]
      · linarith only [h1618, h1619, h5, h7, hc23, hlam, hphi, u3elo3]
    · linarith only [h1618, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
  · linarith only [h1616, h1617, h7, hlam]

end R2N4
