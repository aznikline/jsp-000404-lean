import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1479 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1480 | h1480
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1481 | h1481
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1482 | h1482
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1483 | h1483
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1484 | h1484
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1485 | h1485
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1486 | h1486
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1487 | h1487
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1488 | h1488
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1489 | h1489
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1490 | h1490
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1491 | h1491
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1492 | h1492
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1493 | h1493
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1494 | h1494
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1495 | h1495
                                · linarith only [h0, h1479, h1488, h1492, h1495, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h1479, h1490, h1491, h1495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h1479, h1490, h1491, h1494, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1486, h1493, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1485, h1492, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1501 | h1501
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1502 | h1502
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1503 | h1503
                              · linarith only [h0, h1479, h1488, h1491, h1501, h1503, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1505 | h1505
                                · linarith only [h1490, h1491, h1505, hlam]
                                · rcases h0bigk with h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h0, hlam, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h0, h1485, h1487, h1490, h1491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h0, h1487, h1490, h1491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1479, h1485, h1487, h1490, h1491, hc02, hc13, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1, u3elo0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h0, h1485, h1487, h1490, h1491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h0, h1487, h1490, h1491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h0, h1487, h1490, h1491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1479, hlam, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1482, hlam, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1487, h1490, h1491, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1507_1, u3elo0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1507_1, u3elo0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1480, hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1483, hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1485, hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h0, h1480, h1481, h1489, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1481, hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1484, hlam, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1486, hlam, p1507_0]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [h1487, hlam, p1507_1]
                                  · have p1507_0 := h1507c.1
                                    have p1507_1 := h1507c.2.1
                                    have p1507_2 := h1507c.2.2.1
                                    have p1507_3 := h1507c.2.2.2
                                    linarith only [hlam, p1507_0]
                            · linarith only [h1486, h1501, h1502, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · linarith only [h1485, h1501, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1485, h1488, h1490, hc23, hlam, hphi, u3elo0]
                    · linarith only [h0, h1484, h1489, hlam]
                  · linarith only [h0, h1488, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1538 | h1538
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1539 | h1539
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1540 | h1540
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1541 | h1541
                        · linarith only [h0, h1480, h1487, h1541, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1543 | h1543
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1544 | h1544
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1545 | h1545
                              · linarith only [h1483, h1487, h1545, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1547 | h1547
                                · linarith only [h1480, h1487, h1540, h1547, hlam]
                                · rcases h0bigk with h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c | h1549c
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h0, hlam, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h0, h1479, h1538, h1544, h1547, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h0, h1480, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h0, h1479, h1538, h1544, h1547, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    rcases p1549_3 (m.d 0 1) (by simp) with h1558 | h1558
                                    · linarith only [h0, h1558, hlam]
                                    · linarith only [h1480, h1558, hlam]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    rcases p1549_3 (m.d 0 1) (by simp) with h1561 | h1561
                                    · linarith only [h0, h1561, hlam]
                                    · linarith only [h1481, h1561, hlam]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1479, hlam, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1482, hlam, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1480, h1540, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1549_1, u3elo0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1481, h1539, h1543, h1545, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1549_1, u3elo0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1480, hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1483, hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1485, hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1487, hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1481, hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1484, hlam, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h1486, hlam, p1549_0]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [h0, h1480, h1481, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1549_1]
                                  · have p1549_0 := h1549c.1
                                    have p1549_1 := h1549c.2.1
                                    have p1549_2 := h1549c.2.2.1
                                    have p1549_3 := h1549c.2.2.2
                                    linarith only [hlam, p1549_0]
                            · linarith only [h1486, h1544, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1540, h1543, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1485, h1540, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h1484, h1539, hlam]
                  · linarith only [h0, h1538, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1584 | h1584
                · linarith only [h1485, h1486, h1584, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1586 | h1586
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1587 | h1587
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1588 | h1588
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1589 | h1589
                        · linarith only [h0, h1479, h1584, h1588, h1589, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1591 | h1591
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1592 | h1592
                            · linarith only [h1479, h1486, h1586, h1592, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1594 | h1594
                              · linarith only [h1483, h1485, h1486, h1584, h1594, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1596 | h1596
                                · linarith only [h0, h1480, h1584, h1588, h1596, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h0bigk with h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h0, hlam, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h0, h1479, h1586, h1591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h0, h1479, h1486, h1586, h1591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h0, h1479, h1586, h1591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    rcases p1598_3 (m.d 0 1) (by simp) with h1607 | h1607
                                    · linarith only [h0, h1607, hlam]
                                    · linarith only [h1480, h1607, hlam]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h0, h1479, h1486, h1586, h1591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1479, hlam, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1482, hlam, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1480, h1486, h1588, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1598_1, u3elo4]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1486, hlam, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1480, hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1483, hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1485, hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1584, hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1481, hlam, p1598_0]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1484, hlam, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1479, h1586, h1591, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1598_1]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [h1480, h1486, h1588, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1598_1, u3elo4]
                                  · have p1598_0 := h1598c.1
                                    have p1598_1 := h1598c.2.1
                                    have p1598_2 := h1598c.2.2.1
                                    have p1598_3 := h1598c.2.2.2
                                    linarith only [hlam, p1598_0]
                          · linarith only [h1485, h1591, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1485, h1486, h1586, h1588, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1484, h1587, hlam]
                  · linarith only [h0, h1586, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1630 | h1630
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1631 | h1631
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1632 | h1632
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1633 | h1633
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1634 | h1634
                      · linarith only [h1479, h1485, h1634, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1636 | h1636
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1637 | h1637
                          · linarith only [h1479, h1485, h1632, h1637, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1639 | h1639
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1640 | h1640
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1641 | h1641
                                · rcases h0bigk with h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [hlam, p1642_0]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h0, hlam, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1479, h1632, h1639, h1641, hc01, hc45, hlam, hphi, ht0b, ht5b, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h0, h1479, h1485, h1632, h1639, h1641, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [hlam, p1642_0]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h0, h1479, h1632, h1639, h1641, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h0, h1479, h1485, h1632, h1639, h1641, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    rcases p1642_3 (m.d 0 1) (by simp) with h1652 | h1652
                                    · linarith only [h0, h1652, hlam]
                                    · linarith only [h1481, h1652, hlam]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1479, hlam, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1482, hlam, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [hlam, p1642_0]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1485, hlam, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1481, h1485, h1633, h1639, h1641, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1642_1, u3elo3]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1480, hlam, p1642_0]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1483, hlam, p1642_0]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1479, h1632, h1639, h1641, hc04, hc45, hlam, hphi, ht0b, ht5b, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [hlam, p1642_0]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1481, h1485, h1633, h1639, h1641, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1642_1, u3elo3]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1481, hlam, p1642_0]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1484, hlam, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1630, hlam, p1642_0]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [h1631, hlam, p1642_1]
                                  · have p1642_0 := h1642c.1
                                    have p1642_1 := h1642c.2.1
                                    have p1642_2 := h1642c.2.2.1
                                    have p1642_3 := h1642c.2.2.2
                                    linarith only [hlam, p1642_0]
                                · linarith only [h1479, h1485, h1631, h1632, h1639, h1641, hc04, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h1481, h1636, h1637, h1639, h1640, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1485, h1630, h1639, hc23, hlam, hphi, u3elo3]
                        · linarith only [h1485, h1630, h1631, h1634, h1636, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1484, h1633, hlam]
                  · linarith only [h0, h1632, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1485, h1630, h1631, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1677 | h1677
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1678 | h1678
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1679 | h1679
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
                      · linarith only [h0, h1479, h1485, h1680, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1682 | h1682
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1683 | h1683
                          · linarith only [h1479, h1485, h1678, h1683, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1685 | h1685
                            · linarith only [h1479, h1630, h1678, h1685, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1687 | h1687
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1688 | h1688
                                · rcases h0bigk with h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [hlam, p1689_0]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h0, hlam, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h0, h1479, h1630, h1677, h1678, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h0, h1479, h1630, h1678, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [hlam, p1689_0]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    rcases p1689_3 (m.d 0 1) (by simp) with h1697 | h1697
                                    · linarith only [h0, h1697, hlam]
                                    · linarith only [h1479, h1697, hlam]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h0, h1480, h1682, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    rcases p1689_3 (m.d 0 1) (by simp) with h1701 | h1701
                                    · linarith only [h0, h1701, hlam]
                                    · linarith only [h1481, h1701, hlam]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1479, hlam, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1482, hlam, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [hlam, p1689_0]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1485, hlam, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1630, hlam, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1480, hlam, p1689_0]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1483, hlam, p1689_0]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h0, h1479, h1480, h1678, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [hlam, p1689_0]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1479, h1485, h1630, h1678, hc23, hlam, hphi, p1689_1, u3elo3]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1481, hlam, p1689_0]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1484, hlam, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h0, h1479, h1481, h1678, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [h1677, hlam, p1689_1]
                                  · have p1689_0 := h1689c.1
                                    have p1689_1 := h1689c.2.1
                                    have p1689_2 := h1689c.2.2.1
                                    have p1689_3 := h1689c.2.2.2
                                    linarith only [hlam, p1689_0]
                                · linarith only [h1483, h1485, h1687, h1688, hlam]
                              · linarith only [h0, h1480, h1682, h1687, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1485, h1677, h1678, h1680, h1682, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1484, h1679, hlam]
                  · linarith only [h0, h1678, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1724 | h1724
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1725 | h1725
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1726 | h1726
                      · linarith only [h1479, h1485, h1726, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1728 | h1728
                        · linarith only [h0, h1480, h1677, h1728, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1730 | h1730
                          · linarith only [h1479, h1485, h1724, h1730, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1732 | h1732
                            · linarith only [h1481, h1630, h1724, h1726, h1728, h1732, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1734 | h1734
                              · linarith only [h1483, h1677, h1734, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1736 | h1736
                                · linarith only [h1480, h1677, h1724, h1726, h1736, hc23, hlam, hphi, u3elo3]
                                · rcases h0bigk with h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [hlam, p1738_0]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h0, hlam, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h0, h1479, h1724, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h0, h1480, h1724, h1726, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1481, hc02, hc15, hlam, hphi, ht0b, ht5b, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [hlam, p1738_0]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    rcases p1738_3 (m.d 0 1) (by simp) with h1746 | h1746
                                    · linarith only [h0, h1746, hlam]
                                    · linarith only [h1479, h1746, hlam]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    rcases p1738_3 (m.d 0 1) (by simp) with h1749 | h1749
                                    · linarith only [h0, h1749, hlam]
                                    · linarith only [h1480, h1749, hlam]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    rcases p1738_3 (m.d 0 1) (by simp) with h1752 | h1752
                                    · linarith only [h0, h1752, hlam]
                                    · linarith only [h1481, h1752, hlam]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1479, hlam, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1482, hlam, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [hlam, p1738_0]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1485, hlam, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1630, hlam, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1480, hlam, p1738_0]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1483, hlam, p1738_0]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h0, h1479, h1480, h1724, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [hlam, p1738_0]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1677, hlam, p1738_0]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1481, hlam, p1738_0]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1484, hlam, p1738_1]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1479, h1630, h1724, hc23, hlam, hphi, p1738_1, u3elo4]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [h1630, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1738_1, u3elo4]
                                  · have p1738_0 := h1738c.1
                                    have p1738_1 := h1738c.2.1
                                    have p1738_2 := h1738c.2.2.1
                                    have p1738_3 := h1738c.2.2.2
                                    linarith only [hlam, p1738_0]
                    · linarith only [h0, h1484, h1725, hlam]
                  · linarith only [h0, h1479, h1724, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h1481, h1484, hlam]
        · linarith only [h0, h1480, h1483, hlam]
      · linarith only [h0, h1479, h1482, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1775 | h1775
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1776 | h1776
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1777 | h1777
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1778 | h1778
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1779 | h1779
              · linarith only [h1479, h1481, h1779, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1781 | h1781
                · linarith only [h1479, h1481, h1778, h1781, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1783 | h1783
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1784 | h1784
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1785 | h1785
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1786 | h1786
                        · linarith only [h1480, h1481, h1781, h1784, h1786, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1479, h1481, h1785, h1786, hc34, hc45, hlam, hphi]
                      · linarith only [h1778, h1779, h1785, hc13, hlam, hphi, u3elo4]
                    · linarith only [h0, h1777, h1784, hlam]
                  · linarith only [h0, h1479, h1783, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1792 | h1792
              · linarith only [h1480, h1481, h1778, h1792, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1794 | h1794
                · linarith only [h1480, h1481, h1794, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1796 | h1796
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1797 | h1797
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1798 | h1798
                      · linarith only [h1479, h1481, h1778, h1797, h1798, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1800 | h1800
                        · linarith only [h1480, h1481, h1792, h1794, h1800, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1802 | h1802
                          · linarith only [h1479, h1778, h1796, h1802, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1804 | h1804
                            · linarith only [h1479, h1481, h1778, h1792, h1796, h1804, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1806 | h1806
                              · linarith only [h1480, h1481, h1776, h1796, h1798, h1800, h1806, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1808 | h1808
                                · linarith only [h1480, h1481, h1796, h1798, h1800, h1808, hc23, hlam, hphi, u3elo3]
                                · rcases h0bigk with h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [hlam, p1810_0]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h0, hlam, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1481, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1479, h1481, h1778, h1796, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1481, hlam, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [hlam, p1810_0]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    rcases p1810_3 (m.d 0 1) (by simp) with h1818 | h1818
                                    · linarith only [h0, h1818, hlam]
                                    · linarith only [h1479, h1818, hlam]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    rcases p1810_3 (m.d 0 1) (by simp) with h1821 | h1821
                                    · linarith only [h0, h1821, hlam]
                                    · linarith only [h1480, h1821, hlam]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h0, h1480, h1481, h1796, h1798, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1479, hlam, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1775, hlam, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [hlam, p1810_0]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1778, hlam, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1792, hlam, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1480, hlam, p1810_0]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1776, hlam, p1810_0]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h0, h1479, h1480, h1796, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [hlam, p1810_0]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1794, hlam, p1810_0]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1479, h1796, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1777, hlam, p1810_1]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1479, h1792, h1796, hc23, hlam, hphi, p1810_1, u3elo4]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [h1792, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1810_1, u3elo4]
                                  · have p1810_0 := h1810c.1
                                    have p1810_1 := h1810c.2.1
                                    have p1810_2 := h1810c.2.2.1
                                    have p1810_3 := h1810c.2.2.2
                                    linarith only [hlam, p1810_0]
                    · linarith only [h0, h1777, h1792, h1797, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h1479, h1796, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1842 | h1842
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1843 | h1843
              · linarith only [h0, h1479, h1777, h1843, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1845 | h1845
                · linarith only [h0, h1479, h1777, h1842, h1845, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1847 | h1847
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1848 | h1848
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1849 | h1849
                      · linarith only [h0, h1479, h1777, h1848, h1849, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1842, h1843, h1847, h1849, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1852 | h1852
                      · linarith only [h0, h1479, h1848, h1852, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1842, h1843, h1852, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h1847, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1856 | h1856
              · linarith only [h1775, h1777, h1842, h1856, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1858 | h1858
                · linarith only [h0, h1480, h1777, h1858, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1860 | h1860
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1861 | h1861
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1862 | h1862
                      · linarith only [h1842, h1862, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1864 | h1864
                        · linarith only [h0, h1480, h1777, h1842, h1858, h1861, h1864, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1866 | h1866
                          · linarith only [h0, h1479, h1777, h1860, h1861, h1866, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1868 | h1868
                            · linarith only [h0, h1480, h1777, h1856, h1860, h1862, h1868, hlam]
                            · linarith only [h0, h1480, h1777, h1862, h1868, hc13, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1871 | h1871
                      · linarith only [h1479, h1842, h1871, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1873 | h1873
                        · linarith only [h0, h1480, h1861, h1873, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1875 | h1875
                          · linarith only [h1479, h1842, h1860, h1875, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1877 | h1877
                            · linarith only [h0, h1480, h1860, h1861, h1871, h1877, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h1480, h1860, h1861, h1871, h1877, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h1860, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h0, h1480, h1776, hlam]
      · linarith only [h0, h1479, h1775, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1883 | h1883
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1884 | h1884
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1885 | h1885
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1886 | h1886
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1887 | h1887
            · linarith only [h1479, h1480, h1887, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1889 | h1889
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1890 | h1890
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1891 | h1891
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1892 | h1892
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1893 | h1893
                      · linarith only [h0, h1479, h1887, h1893, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1479, h1480, h1893, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1479, h1886, h1891, h1892, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1891, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1479, h1480, h1887, h1889, h1890, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1899 | h1899
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1900 | h1900
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1901 | h1901
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1902 | h1902
                      · linarith only [h0, h1479, h1887, h1902, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1479, h1480, h1900, h1902, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1886, h1901, hlam]
                  · linarith only [h0, h1900, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1480, h1883, h1899, hlam]
          · linarith only [h0, h1883, h1886, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1909 | h1909
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1910 | h1910
            · linarith only [h0, h1479, h1885, h1910, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1912 | h1912
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1913 | h1913
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1914 | h1914
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1915 | h1915
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1916 | h1916
                      · linarith only [h0, h1479, h1885, h1910, h1916, hlam]
                      · linarith only [h1479, h1480, h1916, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1479, h1885, h1909, h1910, h1914, h1915, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1914, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1884, h1885, h1910, h1912, h1913, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1922 | h1922
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1923 | h1923
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1924 | h1924
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1925 | h1925
                      · linarith only [h0, h1479, h1910, h1925, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1479, h1480, h1923, h1925, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1479, h1885, h1909, h1910, h1923, h1924, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1923, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h0, h1883, h1885, h1922, hlam]
          · linarith only [h0, h1883, h1909, hlam]
      · linarith only [h0, h1479, h1884, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1933 | h1933
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1934 | h1934
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1935 | h1935
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1936 | h1936
            · linarith only [h1479, h1480, h1936, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1938 | h1938
              · linarith only [h1479, h1883, h1938, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1940 | h1940
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1941 | h1941
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1942 | h1942
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1943 | h1943
                      · linarith only [h1479, h1883, h1936, h1942, h1943, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1479, h1480, h1941, h1943, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1479, h1935, h1941, h1942, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1941, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1948 | h1948
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1949 | h1949
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1950 | h1950
                      · linarith only [h1479, h1480, h1940, h1950, hc34, hc45, hlam, hphi]
                      · linarith only [h1479, h1480, h1950, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1935, h1949, hlam]
                  · linarith only [h0, h1948, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1955 | h1955
            · linarith only [h1479, h1480, h1955, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1957 | h1957
              · linarith only [h1479, h1883, h1957, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1959 | h1959
                · linarith only [h1934, h1935, h1959, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1961 | h1961
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1962 | h1962
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1963 | h1963
                      · linarith only [h1479, h1480, h1934, h1935, h1955, h1962, h1963, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1479, h1480, h1961, h1963, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1966 | h1966
                      · linarith only [h0, h1479, h1962, h1966, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1479, h1480, h1961, h1966, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1961, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1970 | h1970
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1971 | h1971
            · linarith only [h0, h1479, h1934, h1971, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1973 | h1973
              · linarith only [h1479, h1883, h1971, h1973, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1975 | h1975
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1976 | h1976
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1977 | h1977
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1978 | h1978
                      · linarith only [h1479, h1883, h1971, h1977, h1978, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1479, h1480, h1976, h1978, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1479, h1934, h1970, h1971, h1976, h1977, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1976, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1934, h1970, h1975, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1984 | h1984
            · linarith only [h0, h1479, h1934, h1984, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1986 | h1986
              · linarith only [h0, h1479, h1970, h1986, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1988 | h1988
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1989 | h1989
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1990 | h1990
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1991 | h1991
                      · linarith only [h0, h1479, h1970, h1984, h1990, h1991, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1479, h1480, h1989, h1991, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1994 | h1994
                      · linarith only [h1479, h1480, h1984, h1988, h1994, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1479, h1480, h1989, h1994, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1479, h1989, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1998 | h1998
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1999 | h1999
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2000 | h2000
                      · linarith only [h1479, h1480, h1988, h2000, hc34, hc45, hlam, hphi]
                      · linarith only [h1479, h1480, h2000, hc13, hlam, hphi, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2003 | h2003
                      · linarith only [h0, h1479, h1999, h2003, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1479, h1480, h1998, h2003, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1998, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h0, h1479, h1933, hc13, hlam, hphi, u3elo2]

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1479 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2008 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2009 | h2009
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2010 | h2010
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2011 | h2011
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2012 | h2012
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2013 | h2013
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2014 | h2014
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2015 | h2015
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2016 | h2016
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2017 | h2017
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2018 | h2018
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2019 | h2019
                      · linarith only [h1479, h2008, h2019, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h1479, h2008, h2015, h2019, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h1479, h2018, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2012, h2017, hlam]
                · linarith only [h0, h2010, h2016, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2025 | h2025
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2026 | h2026
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2027 | h2027
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2028 | h2028
                      · linarith only [h1479, h2008, h2015, h2028, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2030 | h2030
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2031 | h2031
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2032 | h2032
                            · linarith only [h2011, h2015, h2032, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2034 | h2034
                              · linarith only [h1479, h2008, h2015, h2027, h2034, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases h0bigk with h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h0, hlam, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1479, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1479, h2008, h2027, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2036_1, u3elo1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1479, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2036_1, u3elo1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h0, h1479, h2008, h2027, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  rcases p2036_3 (m.d 0 1) (by simp) with h2045 | h2045
                                  · linarith only [h0, h2045, hlam]
                                  · linarith only [h2008, h2045, hlam]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  rcases p2036_3 (m.d 0 1) (by simp) with h2048 | h2048
                                  · linarith only [h0, h2048, hlam]
                                  · linarith only [h2009, h2048, hlam]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1479, h2009, h2026, h2030, h2032, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2036_1, u3elo1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2010, hlam, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1479, h2008, h2027, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2036_1, u3elo1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1479, h2009, h2026, h2030, h2032, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2036_1, u3elo1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2008, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2011, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2013, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2015, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2009, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2012, hlam, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2014, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h0, h2008, h2009, h2027, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                          · linarith only [h1479, h2014, h2031, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1479, h2008, h2027, h2030, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1479, h2009, h2013, h2015, h2027, hlam]
                  · linarith only [h0, h2012, h2026, hlam]
                · linarith only [h0, h2025, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h1479, h2009, h2014, hlam]
          · linarith only [h1479, h2008, h2013, hlam]
        · linarith only [h0, h2009, h2012, hlam]
      · linarith only [h1479, h2008, h2010, h2011, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2075 | h2075
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2076 | h2076
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2077 | h2077
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2078 | h2078
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2079 | h2079
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2080 | h2080
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2081 | h2081
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2082 | h2082
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2083 | h2083
                      · linarith only [h0, h2008, h2010, h2080, h2083, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h0, h2008, h2010, h2079, h2080, h2083, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h0, h2010, h2080, h2082, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2008, h2010, h2079, h2080, h2081, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h2008, h2079, h2080, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2089 | h2089
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2090 | h2090
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2091 | h2091
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2092 | h2092
                      · linarith only [h0, h2008, h2010, h2079, h2092, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2094 | h2094
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2095 | h2095
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2096 | h2096
                            · linarith only [h2010, h2075, h2079, h2089, h2096, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2098 | h2098
                              · linarith only [h2008, h2079, h2091, h2098, hlam]
                              · rcases h0bigk with h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c | h2100c
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h0, hlam, p2100_1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h1479, hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h0, h2008, h2010, h2089, h2091, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h0, h2009, h2010, h2089, h2090, h2094, h2096, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2010, h2089, hc01, hlam, hphi, ht12, ht23, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2010, hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2008, h2010, h2089, h2091, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2009, h2010, h2089, h2090, h2094, h2096, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2009, h2010, h2089, h2090, h2094, h2096, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2010, h2089, hc02, hlam, hphi, ht23, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2008, h2010, h2089, h2091, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2009, h2010, h2089, h2090, h2094, h2096, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2100_1, u3elo1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2008, hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2075, hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2077, hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2079, hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2009, hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2076, hlam, p2100_1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h2078, hlam, p2100_0]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [h0, h2008, h2009, h2091, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2100_1]
                                · have p2100_0 := h2100c.1
                                  have p2100_1 := h2100c.2.1
                                  have p2100_2 := h2100c.2.2.1
                                  have p2100_3 := h2100c.2.2.2
                                  linarith only [hlam, p2100_0]
                          · linarith only [h0, h2010, h2095, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h2009, h2010, h2091, h2092, h2094, hlam]
                    · linarith only [h1479, h2009, h2090, h2091, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h2008, h2010, h2076, h2089, h2090, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                · linarith only [h0, h2008, h2089, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h0, h2009, h2010, h2078, hlam]
          · linarith only [h0, h2008, h2010, h2077, hlam]
        · linarith only [h0, h2009, h2076, hlam]
      · linarith only [h0, h2008, h2075, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2135 | h2135
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2136 | h2136
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2137 | h2137
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2138 | h2138
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2139 | h2139
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2140 | h2140
              · linarith only [h2008, h2009, h2140, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2142 | h2142
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2143 | h2143
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2144 | h2144
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2145 | h2145
                      · linarith only [h1479, h2008, h2140, h2145, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2147 | h2147
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2148 | h2148
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2149 | h2149
                            · linarith only [h2008, h2009, h2136, h2145, h2149, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2151 | h2151
                              · linarith only [h2008, h2009, h2144, h2145, h2151, hlam]
                              · rcases h0bigk with h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h0, hlam, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h1479, hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2009, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2009, hlam, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h0, h1479, h2008, h2144, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  rcases p2153_3 (m.d 0 1) (by simp) with h2162 | h2162
                                  · linarith only [h0, h2162, hlam]
                                  · linarith only [h2008, h2162, hlam]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h0, h2008, h2009, h2144, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2008, h2144, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2135, hlam, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h1479, h2008, h2144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2153_1, u3elo1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h1479, h2008, h2009, h2144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2153_1, u3elo1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2008, hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2136, hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2138, hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2140, hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2008, h2144, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2137, hlam, p2153_1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h2139, hlam, p2153_0]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [h1479, h2008, h2139, h2144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2153_1, u3elo1]
                                · have p2153_0 := h2153c.1
                                  have p2153_1 := h2153c.2.1
                                  have p2153_2 := h2153c.2.2.1
                                  have p2153_3 := h2153c.2.2.2
                                  linarith only [hlam, p2153_0]
                          · linarith only [h1479, h2139, h2148, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1479, h2008, h2144, h2147, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1479, h2144, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2137, h2143, hlam]
                · linarith only [h0, h2008, h2142, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2186 | h2186
              · linarith only [h2008, h2009, h2186, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2188 | h2188
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2189 | h2189
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2190 | h2190
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2191 | h2191
                      · linarith only [h2008, h2009, h2186, h2191, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2193 | h2193
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2194 | h2194
                          · linarith only [h1479, h2139, h2194, hc01, hlam, hphi, ht12, ht23, u3elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2196 | h2196
                            · linarith only [h0, h2008, h2009, h2136, h2190, h2191, h2196, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2198 | h2198
                              · linarith only [h2008, h2009, h2190, h2191, h2198, hlam]
                              · rcases h0bigk with h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h0, hlam, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h1479, hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2008, h2009, h2190, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2009, hlam, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h0, h1479, h2008, h2190, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  rcases p2200_3 (m.d 0 1) (by simp) with h2209 | h2209
                                  · linarith only [h0, h2209, hlam]
                                  · linarith only [h2008, h2209, hlam]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h0, h1479, h2008, h2139, h2190, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2008, h2190, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2135, hlam, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h1479, h2008, h2190, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2200_1, u3elo1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2139, hlam, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2008, hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2136, hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2138, hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2186, hlam, p2200_0]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2008, h2190, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2137, hlam, p2200_1]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2139, hc03, hlam, hphi, p2200_1, u3elo4]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [h2008, h2139, h2190, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2200_1, u3elo4]
                                · have p2200_0 := h2200c.1
                                  have p2200_1 := h2200c.2.1
                                  have p2200_2 := h2200c.2.2.1
                                  have p2200_3 := h2200c.2.2.2
                                  linarith only [hlam, p2200_0]
                        · linarith only [h1479, h2008, h2190, h2193, hc23, hlam, hphi, u3elo0]
                    · linarith only [h1479, h2008, h2190, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h0, h2008, h2137, h2139, h2189, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h0, h2008, h2188, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h1479, h2008, h2138, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2233 | h2233
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2234 | h2234
            · linarith only [h2135, h2137, h2234, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2236 | h2236
              · linarith only [h1479, h2008, h2135, h2137, h2236, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2238 | h2238
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2239 | h2239
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2240 | h2240
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2241 | h2241
                      · linarith only [h1479, h2008, h2234, h2236, h2241, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2243 | h2243
                        · linarith only [h2135, h2137, h2239, h2243, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1479, h2008, h2234, h2240, h2243, hc23, hlam, hphi, u3elo4]
                    · linarith only [h1479, h2008, h2240, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2247 | h2247
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2248 | h2248
                      · linarith only [h1479, h2008, h2234, h2248, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2250 | h2250
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2251 | h2251
                          · linarith only [h1479, h2008, h2135, h2234, h2247, h2251, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h2008, h2239, h2247, h2251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1479, h2008, h2238, h2239, h2247, h2250, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h1479, h2247, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2008, h2238, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h1479, h2008, h2233, hlam]
      · linarith only [h0, h2008, h2136, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2259 | h2259
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2260 | h2260
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2261 | h2261
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2262 | h2262
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2263 | h2263
              · linarith only [h2008, h2009, h2263, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2265 | h2265
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2266 | h2266
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2267 | h2267
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2268 | h2268
                      · linarith only [h2008, h2009, h2135, h2260, h2263, h2265, h2268, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2270 | h2270
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2271 | h2271
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2272 | h2272
                            · linarith only [h2008, h2009, h2259, h2268, h2272, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2274 | h2274
                              · linarith only [h2008, h2009, h2267, h2268, h2274, hlam]
                              · rcases h0bigk with h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c | h2276c
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h0, hlam, p2276_1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h1479, hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2009, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p2276_1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2009, hlam, p2276_1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2135, h2265, hc01, hlam, hphi, ht12, ht23, p2276_1, u3elo1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2135, hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2008, h2135, h2265, h2267, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2276_1, u3elo1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2009, h2135, h2265, hc01, hlam, hphi, ht12, ht23, p2276_1, u3elo1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2276_1, u3elo0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2135, h2265, hc02, hlam, hphi, ht23, p2276_1, u3elo1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2008, h2135, h2265, h2267, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2276_1, u3elo1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2008, h2009, h2135, h2265, h2267, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2276_1, u3elo1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2008, hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2259, hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2261, hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2263, hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2008, h2260, h2267, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2276_1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2260, hlam, p2276_1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2262, hlam, p2276_0]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [h2008, h2135, h2260, h2265, h2267, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2276_1, u3elo1]
                                · have p2276_0 := h2276c.1
                                  have p2276_1 := h2276c.2.1
                                  have p2276_2 := h2276c.2.2.1
                                  have p2276_3 := h2276c.2.2.2
                                  linarith only [hlam, p2276_0]
                          · linarith only [h2135, h2271, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2135, h2270, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h2008, h2009, h2135, h2260, h2261, h2265, h2267, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h2008, h2260, h2266, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h2008, h2265, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h2135, h2260, h2262, hlam]
          · linarith only [h0, h2008, h2135, h2261, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2309 | h2309
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2310 | h2310
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2311 | h2311
              · linarith only [h0, h2008, h2260, h2311, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2313 | h2313
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2314 | h2314
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2315 | h2315
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2316 | h2316
                      · linarith only [h0, h2008, h2135, h2311, h2313, h2316, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2318 | h2318
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2319 | h2319
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2320 | h2320
                            · linarith only [h2008, h2009, h2259, h2316, h2320, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2322 | h2322
                              · linarith only [h2008, h2259, h2260, h2314, h2315, h2316, h2322, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c | h2324c
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h0, hlam, p2324_1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h1479, hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h0, h2260, h2313, h2319, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2324_1, u3elo1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2009, hlam, p2324_1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2260, h2313, h2319, hc01, hlam, hphi, ht12, ht23, p2324_1, u3elo1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2135, hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2008, h2260, h2313, h2315, h2319, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2324_1, u3elo1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2260, hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2008, h2315, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2324_1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2135, h2313, hc02, hlam, hphi, ht23, p2324_1, u3elo1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2008, h2135, h2313, h2315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2324_1, u3elo1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h0, h2008, h2135, h2260, h2313, h2315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2324_1, u3elo1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2008, hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2259, hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2309, hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2311, hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2008, h2315, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2324_1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h0, h2008, h2260, h2313, h2315, h2319, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2324_1, u3elo1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2310, hlam, p2324_0]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [h2008, h2260, h2313, h2315, h2319, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2324_1, u3elo1]
                                · have p2324_0 := h2324c.1
                                  have p2324_1 := h2324c.2.1
                                  have p2324_2 := h2324c.2.2.1
                                  have p2324_3 := h2324c.2.2.2
                                  linarith only [hlam, p2324_0]
                          · linarith only [h2135, h2310, h2319, hlam]
                        · linarith only [h0, h2008, h2135, h2310, h2315, h2318, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h2008, h2135, h2313, h2315, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h0, h2008, h2135, h2313, h2314, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h2008, h2313, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2355 | h2355
              · linarith only [h0, h2008, h2135, h2310, h2355, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2357 | h2357
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2358 | h2358
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2359 | h2359
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2360 | h2360
                      · linarith only [h0, h2008, h2135, h2310, h2355, h2360, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2362 | h2362
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2363 | h2363
                          · linarith only [h0, h2135, h2310, h2357, h2363, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h0, h2008, h2135, h2359, h2363, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h2008, h2135, h2359, h2362, hlam]
                    · linarith only [h1479, h2359, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2008, h2135, h2357, h2358, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h2008, h2357, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h0, h2008, h2135, h2309, hlam]
      · linarith only [h0, h2008, h2259, hlam]

end R2N4
