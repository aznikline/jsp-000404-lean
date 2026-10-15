import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1464 | h1464
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1465 | h1465
    · linarith only [h0, h1, h1465, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1467 | h1467
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1468 | h1468
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1469 | h1469
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1470 | h1470
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1471 | h1471
              · linarith only [h0, h1, h1465, h1471, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1473 | h1473
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1474 | h1474
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1475 | h1475
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1476 | h1476
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1477 | h1477
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1478 | h1478
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1479 | h1479
                            · linarith only [h0, h1, h1471, h1473, h1479, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h1464, h1476, h1479, hc24, hlam, hphi, u4elo0]
                          · linarith only [h0, h1, h1471, h1478, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h1471, h1473, h1477, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1470, h1474, h1476, hc34, hlam, hphi, u4elo0]
                    · linarith only [h0, h1, h1467, h1469, h1470, h1475, hc03, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h1474, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h1, h1467, h1471, h1473, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1488 | h1488
              · linarith only [h0, h1465, h1488, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1490 | h1490
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1491 | h1491
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1492 | h1492
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1493 | h1493
                      · linarith only [h1464, h1470, h1493, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1495 | h1495
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1496 | h1496
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1497 | h1497
                            · linarith only [h0, h1, h1470, h1488, h1490, h1497, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1499 | h1499
                              · linarith only [h1464, h1470, h1490, h1495, h1499, hlam]
                              · rcases h3bigk with h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c | h1501c
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1, hlam, p1501_1]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1465, hlam, p1501_1]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  rcases p1501_3 (m.d 0 3) (by simp) with h1505 | h1505
                                  · rcases p1501_3 (m.d 1 3) (by simp) with h1506 | h1506
                                    · rcases p1501_3 (m.d 2 3) (by simp) with h1507 | h1507
                                      · rcases p1501_3 (m.d 3 4) (by simp) with h1508 | h1508
                                        · linarith only [h1508, hlam, p1501_0]
                                        · rcases p1501_3 (m.d 3 5) (by simp) with h1510 | h1510
                                          · linarith only [h1469, h1510, hlam]
                                          · linarith only [h1499, h1510, hlam]
                                      · linarith only [h1495, h1507, hlam]
                                    · linarith only [h1491, h1506, hlam]
                                  · linarith only [h1505, hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  rcases p1501_3 (m.d 0 3) (by simp) with h1516 | h1516
                                  · rcases p1501_3 (m.d 1 3) (by simp) with h1517 | h1517
                                    · rcases p1501_3 (m.d 2 3) (by simp) with h1518 | h1518
                                      · rcases p1501_3 (m.d 3 4) (by simp) with h1519 | h1519
                                        · linarith only [h1468, h1519, hlam]
                                        · rcases p1501_3 (m.d 3 5) (by simp) with h1521 | h1521
                                          · linarith only [h1521, hlam, p1501_0]
                                          · rcases h3emin with h1523 | h1523 | h1523 | h1523 | h1523
                                            · rcases h4bigk with h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1470, h1490, h1495, hc34, hlam, hphi, p1524_1, u4elo4]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1470, h1495, hc34, hlam, hphi, p1524_1, u4elo4]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1470, hc34, hlam, hphi, p1524_1, u4elo4]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1470, hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1464, hlam, p1524_1]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1495, hc34, hlam, hphi, p1524_1, u4elo1]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1464, h1470, hc34, hlam, hphi, p1524_1, u4elo4]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1493, hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1467, hlam, p1524_1]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1490, hlam, p1524_1]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [hc34, hlam, hphi, p1524_1, u4elo2]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1497, hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1468, hlam, p1524_1]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1491, hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1495, hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1499, hlam, p1524_0]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [hc04, hlam, hphi, p1524_1, u4elo4]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1490, hc24, hlam, hphi, p1524_1, u4elo4]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [h1495, hc34, hlam, hphi, p1524_1, u4elo4]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [hc34, hlam, hphi, p1524_1, u4elo4]
                                              · have p1524_0 := h1524c.1
                                                have p1524_1 := h1524c.2.1
                                                have p1524_2 := h1524c.2.2.1
                                                have p1524_3 := h1524c.2.2.2
                                                linarith only [hlam, p1524_0]
                                            · rcases h4bigk with h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c | h1550c
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1490, h1495, hc34, hlam, hphi, p1550_1, u4elo0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1495, hc34, hlam, hphi, p1550_1, u4elo0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hc34, hlam, hphi, p1550_1, u4elo0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1470, hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1464, hlam, p1550_1]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1495, hc34, hlam, hphi, p1550_1, u4elo1]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1464, h1470, hc34, hlam, hphi, p1550_1, u4elo4]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1493, hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1467, hlam, p1550_1]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1490, hlam, p1550_1]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hc34, hlam, hphi, p1550_1, u4elo2]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1497, hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1468, hlam, p1550_1]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1491, hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1495, hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1499, hlam, p1550_0]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hc04, hlam, hphi, p1550_1, u4elo4]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1490, hc24, hlam, hphi, p1550_1, u4elo4]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [h1495, hc34, hlam, hphi, p1550_1, u4elo4]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hc34, hlam, hphi, p1550_1, u4elo4]
                                              · have p1550_0 := h1550c.1
                                                have p1550_1 := h1550c.2.1
                                                have p1550_2 := h1550c.2.2.1
                                                have p1550_3 := h1550c.2.2.2
                                                linarith only [hlam, p1550_0]
                                            · rcases h4bigk with h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c | h1576c
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1490, h1495, hc34, hlam, hphi, p1576_1, u4elo0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1495, hc34, hlam, hphi, p1576_1, u4elo0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hc34, hlam, hphi, p1576_1, u4elo0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1470, hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1464, hlam, p1576_1]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1495, hc34, hlam, hphi, p1576_1, u4elo1]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1464, h1470, hc34, hlam, hphi, p1576_1, u4elo4]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1493, hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1467, hlam, p1576_1]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1490, hlam, p1576_1]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hc34, hlam, hphi, p1576_1, u4elo2]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1497, hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1468, hlam, p1576_1]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1491, hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1495, hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1499, hlam, p1576_0]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hc04, hlam, hphi, p1576_1, u4elo4]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1490, hc24, hlam, hphi, p1576_1, u4elo4]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [h1495, hc34, hlam, hphi, p1576_1, u4elo4]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hc34, hlam, hphi, p1576_1, u4elo4]
                                              · have p1576_0 := h1576c.1
                                                have p1576_1 := h1576c.2.1
                                                have p1576_2 := h1576c.2.2.1
                                                have p1576_3 := h1576c.2.2.2
                                                linarith only [hlam, p1576_0]
                                            · linarith only [h1464, h1490, h1495, h1523, hlam, ht34, u4elo0]
                                            · linarith only [h1523, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1501_1]
                                      · linarith only [h1496, h1518, hlam]
                                    · linarith only [h1492, h1517, hlam]
                                  · linarith only [h1516, hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h0, h1, h1488, hc12, hc23, hlam, hphi, p1501_1]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1488, hlam, p1501_1]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h0, h1, h1490, h1495, hlam, p1501_2]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  rcases p1501_3 (m.d 0 3) (by simp) with h1611 | h1611
                                  · linarith only [h1, h1611, hlam]
                                  · linarith only [h1469, h1611, hlam]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h0, h1, h1490, h1495, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1501_1]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h0, h1, h1490, h1495, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1501_1]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h0, h1, h1488, h1490, h1495, hlam, p1501_2]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  rcases p1501_3 (m.d 0 3) (by simp) with h1618 | h1618
                                  · linarith only [h1465, h1618, hlam]
                                  · linarith only [h1469, h1618, hlam]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1468, hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1491, hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1495, hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1499, hlam, p1501_1]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1469, hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1492, hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1496, hlam, p1501_0]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [h1469, h1470, hc34, hlam, hphi, p1501_1, u4elo4]
                                · have p1501_0 := h1501c.1
                                  have p1501_1 := h1501c.2.1
                                  have p1501_2 := h1501c.2.2.1
                                  have p1501_3 := h1501c.2.2.2
                                  linarith only [hlam, p1501_0]
                          · linarith only [h0, h1, h1469, h1470, h1488, h1490, h1495, h1496, hc34, hlam, hphi, u4elo4]
                        · linarith only [h0, h1, h1488, h1495, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1469, h1490, h1492, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h1490, h1491, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h1467, h1488, h1490, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1636 | h1636
            · linarith only [h0, h1, h1467, h1469, h1636, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1638 | h1638
              · linarith only [h0, h1, h1469, h1636, h1638, hc23, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1640 | h1640
                · linarith only [h0, h1, h1469, h1636, h1640, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h1, h1467, h1469, h1636, h1640, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · linarith only [h1, h1464, h1468, hc14, hlam, hphi, u4elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1644 | h1644
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1645 | h1645
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1646 | h1646
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1647 | h1647
              · linarith only [h0, h1467, h1647, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1649 | h1649
                · linarith only [h0, h1467, h1649, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1651 | h1651
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1652 | h1652
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1653 | h1653
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1654 | h1654
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1655 | h1655
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1656 | h1656
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1657 | h1657
                              · rcases h3bigk with h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1, hlam, p1658_1]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1465, hlam, p1658_1]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  rcases p1658_3 (m.d 0 3) (by simp) with h1662 | h1662
                                  · rcases p1658_3 (m.d 1 3) (by simp) with h1663 | h1663
                                    · rcases p1658_3 (m.d 2 3) (by simp) with h1664 | h1664
                                      · rcases p1658_3 (m.d 3 4) (by simp) with h1665 | h1665
                                        · linarith only [h1665, hlam, p1658_0]
                                        · rcases p1658_3 (m.d 3 5) (by simp) with h1667 | h1667
                                          · linarith only [h1645, h1667, hlam]
                                          · rcases h3emin with h1669 | h1669 | h1669 | h1669 | h1669
                                            · rcases h4bigk with h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c | h1670c
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1651, h1657, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1670_1, u4elo0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1467, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1, h1464, h1657, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1670_1]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                rcases p1670_3 (m.d 0 4) (by simp) with h1675 | h1675
                                                · rcases p1670_3 (m.d 1 4) (by simp) with h1676 | h1676
                                                  · linarith only [h1464, h1676, hlam]
                                                  · linarith only [h1653, h1676, hlam]
                                                · linarith only [h1675, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1464, hlam, p1670_1]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1649, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1657, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1670_1, u4elo1]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1, h1464, h1647, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1670_1]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [hc04, hlam, hphi, p1670_1, u4elo2]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [hc14, hlam, hphi, p1670_1, u4elo2]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1657, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1670_1, u4elo2]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                rcases p1670_3 (m.d 0 4) (by simp) with h1689 | h1689
                                                · linarith only [h1467, h1689, hlam]
                                                · linarith only [h1646, h1689, hlam]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1644, hlam, p1670_1]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1651, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1654, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p1658_1, p1670_1]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1646, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1653, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1656, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [h1657, hlam, p1670_0]
                                              · have p1670_0 := h1670c.1
                                                have p1670_1 := h1670c.2.1
                                                have p1670_2 := h1670c.2.2.1
                                                have p1670_3 := h1670c.2.2.2
                                                linarith only [hlam, p1670_0]
                                            · rcases h4bigk with h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [hc14, hlam, hphi, p1702_1, u4elo0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1467, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1467, hc34, hlam, hphi, p1702_1, u4elo2]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                rcases p1702_3 (m.d 0 4) (by simp) with h1707 | h1707
                                                · rcases p1702_3 (m.d 1 4) (by simp) with h1708 | h1708
                                                  · linarith only [h1464, h1708, hlam]
                                                  · linarith only [h1653, h1708, hlam]
                                                · linarith only [h1707, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1464, hlam, p1702_1]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1649, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1657, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1702_1, u4elo1]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1, h1464, h1647, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1702_1]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [hc04, hlam, hphi, p1702_1, u4elo2]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [hc14, hlam, hphi, p1702_1, u4elo2]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1657, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1702_1, u4elo2]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                rcases p1702_3 (m.d 0 4) (by simp) with h1721 | h1721
                                                · linarith only [h1467, h1721, hlam]
                                                · linarith only [h1646, h1721, hlam]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1644, hlam, p1702_1]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1651, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1654, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1, h1464, h1647, h1651, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1702_1]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1646, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1653, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1656, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [h1657, hlam, p1702_0]
                                              · have p1702_0 := h1702c.1
                                                have p1702_1 := h1702c.2.1
                                                have p1702_2 := h1702c.2.2.1
                                                have p1702_3 := h1702c.2.2.2
                                                linarith only [hlam, p1702_0]
                                            · rcases h4bigk with h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c | h1734c
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [hc14, hlam, hphi, p1734_1, u4elo0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1467, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1467, hc34, hlam, hphi, p1734_1, u4elo2]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                rcases p1734_3 (m.d 0 4) (by simp) with h1739 | h1739
                                                · rcases p1734_3 (m.d 1 4) (by simp) with h1740 | h1740
                                                  · linarith only [h1464, h1740, hlam]
                                                  · linarith only [h1653, h1740, hlam]
                                                · linarith only [h1739, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1464, hlam, p1734_1]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1649, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1657, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1734_1, u4elo1]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1, h1464, h1647, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1734_1]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [hc04, hlam, hphi, p1734_1, u4elo2]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [hc14, hlam, hphi, p1734_1, u4elo2]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1657, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1734_1, u4elo2]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                rcases p1734_3 (m.d 0 4) (by simp) with h1753 | h1753
                                                · linarith only [h1467, h1753, hlam]
                                                · linarith only [h1646, h1753, hlam]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1644, hlam, p1734_1]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1651, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1654, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1, h1464, h1647, h1651, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1734_1]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1646, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1653, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1656, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [h1657, hlam, p1734_0]
                                              · have p1734_0 := h1734c.1
                                                have p1734_1 := h1734c.2.1
                                                have p1734_2 := h1734c.2.2.1
                                                have p1734_3 := h1734c.2.2.2
                                                linarith only [hlam, p1734_0]
                                            · linarith only [h1464, h1651, h1669, hlam, ht34, u4elo0]
                                            · linarith only [h1464, h1652, h1653, h1669, hlam, ht34, u4elo0]
                                      · linarith only [h1654, h1664, hlam]
                                    · linarith only [h1651, h1663, hlam]
                                  · linarith only [h1662, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  rcases p1658_3 (m.d 0 3) (by simp) with h1771 | h1771
                                  · rcases p1658_3 (m.d 1 3) (by simp) with h1772 | h1772
                                    · rcases p1658_3 (m.d 2 3) (by simp) with h1773 | h1773
                                      · rcases p1658_3 (m.d 3 4) (by simp) with h1774 | h1774
                                        · linarith only [h1644, h1774, hlam]
                                        · linarith only [h1657, h1774, hlam]
                                      · linarith only [h1655, h1773, hlam]
                                    · linarith only [h1652, h1772, hlam]
                                  · linarith only [h1771, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h0, h1, h1647, hc12, hc23, hlam, hphi, p1658_1]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1647, hlam, p1658_1]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  rcases p1658_3 (m.d 0 3) (by simp) with h1783 | h1783
                                  · linarith only [h1, h1783, hlam]
                                  · linarith only [h1644, h1783, hlam]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  rcases p1658_3 (m.d 0 3) (by simp) with h1786 | h1786
                                  · linarith only [h1, h1786, hlam]
                                  · linarith only [h1645, h1786, hlam]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1, h1464, h1651, h1657, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1658_1]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1, h1464, h1651, h1657, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1658_1]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  rcases p1658_3 (m.d 0 3) (by simp) with h1792 | h1792
                                  · linarith only [h1465, h1792, hlam]
                                  · linarith only [h1644, h1792, hlam]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  rcases p1658_3 (m.d 0 3) (by simp) with h1795 | h1795
                                  · linarith only [h1465, h1795, hlam]
                                  · linarith only [h1645, h1795, hlam]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1644, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1651, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1654, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1, h1464, h1651, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p1658_1]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1645, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1652, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1655, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [h1657, hlam, p1658_0]
                                · have p1658_0 := h1658c.1
                                  have p1658_1 := h1658c.2.1
                                  have p1658_2 := h1658c.2.2.1
                                  have p1658_3 := h1658c.2.2.2
                                  linarith only [hlam, p1658_0]
                              · linarith only [h1467, h1646, h1657, hc34, hlam, hphi, u4elo2]
                            · linarith only [h1, h1464, h1467, h1647, h1653, h1656, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h1, h1647, h1655, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1464, h1647, h1653, h1654, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1646, h1651, h1653, hc34, hlam, hphi, u4elo0]
                    · linarith only [h1, h1464, h1645, h1646, h1652, hc03, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h1464, h1649, h1651, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1815 | h1815
              · linarith only [h0, h1467, h1646, h1815, hc23, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1817 | h1817
                · linarith only [h0, h1467, h1646, h1817, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1819 | h1819
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1820 | h1820
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1821 | h1821
                      · linarith only [h1, h1464, h1467, h1646, h1821, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1823 | h1823
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1824 | h1824
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1825 | h1825
                            · linarith only [h0, h1467, h1646, h1825, hc12, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h1467, h1825, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h0, h1, h1815, h1824, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1464, h1815, h1819, h1823, hlam]
                    · linarith only [h1, h1464, h1817, h1820, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1464, h1817, h1819, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1832 | h1832
            · linarith only [h1, h1464, h1645, h1832, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1834 | h1834
              · linarith only [h0, h1465, h1834, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1836 | h1836
                · linarith only [h0, h1467, h1836, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1838 | h1838
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1839 | h1839
                    · linarith only [h1, h1464, h1645, h1834, h1836, h1839, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h1464, h1836, h1839, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1464, h1836, h1838, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h1464, h1644, hc14, hlam, hphi, u4elo3]
  · linarith only [h0, h1464, hc12, hlam, hphi, ht23, ht34, u4elo1]

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_13_24_L_I_M_LI_x0_x0 m hb3 hb4 h0 h1
  · exact r1l7_13_24_L_I_M_LI_x0_x1 m hb3 hb4 h0 h1

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1845 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1846 | h1846
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1847 | h1847
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1848 | h1848
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1849 | h1849
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1850 | h1850
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1851 | h1851
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1852 | h1852
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1853 | h1853
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1854 | h1854
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1855 | h1855
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1856 | h1856
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1857 | h1857
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1858 | h1858
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1859 | h1859
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1860 | h1860
                              · linarith only [h0, h1845, h1852, h1857, h1860, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1846, h1853, h1859, h1860, hc34, hlam, hphi, u4elo0]
                            · linarith only [h0, h1845, h1854, h1856, h1859, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h1845, h1855, h1858, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h1845, h1854, h1857, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1851, h1856, hc14, hlam, hphi, u4elo0]
                    · linarith only [h0, h1845, h1850, h1854, h1855, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1868 | h1868
                    · linarith only [h0, h1845, h1849, h1854, h1868, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1870 | h1870
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1871 | h1871
                        · linarith only [h1852, h1854, h1871, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1873 | h1873
                          · linarith only [h1868, h1871, h1873, hc13, hlam, hphi, ht34, u4elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1875 | h1875
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1876 | h1876
                              · rcases h3bigk with h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  rcases p1877_3 (m.d 0 3) (by simp) with h1879 | h1879
                                  · rcases p1877_3 (m.d 1 3) (by simp) with h1880 | h1880
                                    · linarith only [h1845, h1880, hlam]
                                    · rcases p1877_3 (m.d 2 3) (by simp) with h1882 | h1882
                                      · linarith only [h1847, h1882, hlam]
                                      · rcases p1877_3 (m.d 3 4) (by simp) with h1884 | h1884
                                        · linarith only [h1849, h1884, hlam]
                                        · linarith only [h1854, h1884, hlam]
                                  · linarith only [h1845, h1879, hlam]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  rcases p1877_3 (m.d 0 3) (by simp) with h1888 | h1888
                                  · rcases p1877_3 (m.d 1 3) (by simp) with h1889 | h1889
                                    · linarith only [h1845, h1889, hlam]
                                    · linarith only [h1852, h1889, hlam]
                                  · linarith only [h1847, h1888, hlam]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h0, h1845, h1852, h1868, h1876, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1877_1]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h0, h1845, h1852, h1868, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1877_1]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1845, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1868, h1876, hc23, hc34, hlam, hphi, p1877_1]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1854, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1868, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1847, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1852, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1871, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1873, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1849, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h0, h1845, h1849, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1877_1]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h0, h1845, h1849, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1877_1]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h0, h1845, h1849, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1877_1]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1850, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h0, h1845, h1850, h1852, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1877_1]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h0, h1845, h1850, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1877_1]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [h1876, hlam, p1877_0]
                                · have p1877_0 := h1877c.1
                                  have p1877_1 := h1877c.2.1
                                  have p1877_2 := h1877c.2.2.1
                                  have p1877_3 := h1877c.2.2.2
                                  linarith only [hlam, p1877_0]
                              · linarith only [h1851, h1854, h1876, hc14, hlam, hphi, u4elo0]
                            · linarith only [h1870, h1871, h1875, hc23, hlam, hphi, ht34, u4elo1]
                      · linarith only [h1851, h1870, hc14, hlam, hphi, u4elo0]
                · linarith only [h0, h1853, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1845, h1847, h1849, h1852, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1920 | h1920
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1921 | h1921
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1922 | h1922
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1923 | h1923
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1924 | h1924
                      · linarith only [h1851, h1924, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1926 | h1926
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1927 | h1927
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1928 | h1928
                            · linarith only [h1846, h1851, h1921, h1928, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1930 | h1930
                              · linarith only [h1846, h1851, h1921, h1926, h1930, hlam]
                              · rcases h3bigk with h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c | h1932c
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h0, h1845, h1920, h1927, h1930, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h0, h1845, h1927, h1930, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  rcases p1932_3 (m.d 0 3) (by simp) with h1936 | h1936
                                  · rcases p1932_3 (m.d 1 3) (by simp) with h1937 | h1937
                                    · linarith only [h1845, h1937, hlam]
                                    · linarith only [h1922, h1937, hlam]
                                  · linarith only [h1936, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  rcases p1932_3 (m.d 0 3) (by simp) with h1941 | h1941
                                  · rcases p1932_3 (m.d 1 3) (by simp) with h1942 | h1942
                                    · linarith only [h1845, h1942, hlam]
                                    · linarith only [h1923, h1942, hlam]
                                  · linarith only [h1941, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1845, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h0, h1845, h1927, h1930, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h0, h1845, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h0, h1845, h1930, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1847, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1920, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h0, h1845, h1920, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h0, h1845, h1920, h1930, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1849, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1922, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1926, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1930, hlam, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1850, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1923, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h1927, hlam, p1932_0]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [h0, h1845, h1850, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1932_1]
                                · have p1932_0 := h1932c.1
                                  have p1932_1 := h1932c.2.1
                                  have p1932_2 := h1932c.2.2.1
                                  have p1932_3 := h1932c.2.2.2
                                  linarith only [hlam, p1932_0]
                          · linarith only [h0, h1845, h1923, h1927, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1849, h1851, h1926, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1845, h1850, h1922, h1923, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h1849, h1851, h1922, hc13, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h1921, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1847, h1920, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1972 | h1972
            · linarith only [h1849, h1850, h1972, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1974 | h1974
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1975 | h1975
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1976 | h1976
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1977 | h1977
                    · linarith only [h0, h1845, h1850, h1977, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1979 | h1979
                      · linarith only [h1846, h1972, h1979, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1981 | h1981
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1982 | h1982
                          · linarith only [h1845, h1850, h1974, h1982, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1984 | h1984
                            · linarith only [h1846, h1972, h1975, h1984, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1986 | h1986
                              · linarith only [h1972, h1986, hc04, hlam, hphi, u4elo3]
                              · linarith only [h1849, h1850, h1986, hc34, hlam, hphi, u4elo4]
                        · linarith only [h0, h1845, h1976, h1981, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1849, h1850, h1972, h1976, hc13, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h1975, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1845, h1847, h1974, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1993 | h1993
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1994 | h1994
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1995 | h1995
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1996 | h1996
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1997 | h1997
                  · linarith only [h1845, h1849, h1993, h1997, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1999 | h1999
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2000 | h2000
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2001 | h2001
                        · linarith only [h0, h1845, h1846, h1849, h1995, h2000, h2001, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2003 | h2003
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2004 | h2004
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2005 | h2005
                              · rcases h3bigk with h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1849, hc13, hlam, hphi, ht34, p2006_1, u4elo3]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1849, h2003, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2006_1, u4elo3]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1849, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1849, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2006_1, u4elo3]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1845, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1997, h2003, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2006_1, u4elo1]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1997, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1845, h1849, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2006_1, u4elo3]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1847, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1995, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h2001, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1847, h1849, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2006_1, u4elo3]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [hc03, hlam, hphi, ht34, p2006_1, u4elo3]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [hc13, hlam, hphi, ht34, p2006_1, u4elo3]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, p2006_1, u4elo3]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  rcases p2006_3 (m.d 0 3) (by simp) with h2026 | h2026
                                  · linarith only [h1849, h2026, hlam]
                                  · linarith only [h1993, h2026, hlam]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1993, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h1999, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h2003, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [h2005, hlam, p2006_0]
                                · have p2006_0 := h2006c.1
                                  have p2006_1 := h2006c.2.1
                                  have p2006_2 := h2006c.2.2.1
                                  have p2006_3 := h2006c.2.2.2
                                  linarith only [hlam, p2006_0]
                              · linarith only [h1849, h2005, hc03, hlam, hphi, ht34, u4elo4]
                            · linarith only [h0, h1846, h2000, h2004, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1849, h1993, h2003, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h1994, h2000, hc14, hlam, hphi, u4elo0]
                    · linarith only [h1849, h1993, h1999, hc13, hlam, hphi, ht34, u4elo3]
                · linarith only [h0, h1996, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1847, h1995, hlam]
            · linarith only [h1849, h1993, h1994, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2042 | h2042
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2043 | h2043
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2044 | h2044
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2045 | h2045
                  · linarith only [h1845, h1849, h2045, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2047 | h2047
                    · linarith only [h1845, h1993, h2047, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2049 | h2049
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2050 | h2050
                        · linarith only [h1845, h1849, h2043, h2050, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2052 | h2052
                          · linarith only [h1845, h1993, h2043, h2052, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2054 | h2054
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2055 | h2055
                              · rcases h3bigk with h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h1993, h2055, hc13, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h1993, h2055, hc23, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h1849, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h1993, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h1845, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h0, h1845, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2056_1]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2045, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2047, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h1847, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2043, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2050, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2052, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [hc03, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2043, hc23, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h1845, h1993, h2043, hc23, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h1845, h2043, h2055, hc23, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2043, h2055, hc23, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2055, hc23, hlam, hphi, ht34, p2056_1, u4elo3]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [h2055, hlam, p2056_0]
                                · have p2056_0 := h2056c.1
                                  have p2056_1 := h2056c.2.1
                                  have p2056_2 := h2056c.2.2.1
                                  have p2056_3 := h2056c.2.2.2
                                  linarith only [hlam, p2056_0]
                              · linarith only [h1849, h2044, h2054, h2055, hc04, hlam, hphi, u4elo1]
                            · linarith only [h1846, h2049, h2050, h2054, hc23, hlam, hphi, ht34, u4elo0]
                      · linarith only [h1849, h2042, h2049, hc14, hlam, hphi, u4elo3]
                · linarith only [h0, h2044, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1847, h2043, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2087 | h2087
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2088 | h2088
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2089 | h2089
                  · linarith only [h1845, h1849, h2089, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2091 | h2091
                    · linarith only [h1845, h1993, h2091, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2093 | h2093
                      · linarith only [h1846, h2042, h2093, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2095 | h2095
                        · linarith only [h1845, h1849, h2042, h2087, h2095, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2097 | h2097
                          · linarith only [h1845, h1993, h2087, h2097, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2099 | h2099
                            · linarith only [h1846, h2042, h2088, h2099, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2101 | h2101
                              · linarith only [h1849, h2042, h2101, hc03, hlam, hphi, ht34, u4elo3]
                              · linarith only [h1845, h1849, h2087, h2101, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h2088, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1845, h1847, h2087, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h1845, h1848, hc13, hlam, hphi, ht34, u4elo2]
    · linarith only [h0, h1845, h1847, hlam]
  · linarith only [h1845, h1846, hc13, hlam, hphi, ht34, u4elo1]

end R2N4
