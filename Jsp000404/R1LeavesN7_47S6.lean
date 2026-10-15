import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1452 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1453 | h1453
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1454 | h1454
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1455 | h1455
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1456 | h1456
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1457 | h1457
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1458 | h1458
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1459 | h1459
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1460 | h1460
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1461 | h1461
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1462 | h1462
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1463 | h1463
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1464 | h1464
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1465 | h1465
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1466 | h1466
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1467 | h1467
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1468 | h1468
                                · linarith only [h0, h1452, h1461, h1465, h1468, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1460, h1468, hc34, hlam, hphi, u4elo0]
                              · linarith only [h0, h1453, h1464, h1467, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h1452, h1459, h1465, h1466, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1473 | h1473
                            · linarith only [h0, h1452, h1458, h1465, h1473, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1475 | h1475
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1476 | h1476
                                · rcases h0bigk with h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h0, hlam, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h0, h1458, h1473, h1476, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1452, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h0, h1458, h1473, h1476, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h0, h1456, h1475, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h0, h1459, h1473, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1452, hlam, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1455, hlam, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1452, h1458, h1473, h1476, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h0, h1452, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1453, hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1456, hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1458, hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1459, h1473, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1454, hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1457, hlam, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1459, hlam, p1477_0]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [h1460, hlam, p1477_1]
                                  · have p1477_0 := h1477c.1
                                    have p1477_1 := h1477c.2.1
                                    have p1477_2 := h1477c.2.2.1
                                    have p1477_3 := h1477c.2.2.2
                                    linarith only [hlam, p1477_0]
                                · linarith only [h1462, h1475, h1476, hc34, hlam, hphi, u4elo1]
                              · linarith only [h1460, h1475, hc24, hlam, hphi, u4elo0]
                        · linarith only [h1460, h1464, hc14, hlam, hphi, u4elo0]
                      · linarith only [h0, h1457, h1463, hlam]
                    · linarith only [h0, h1462, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1455, h1461, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1509 | h1509
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1510 | h1510
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1511 | h1511
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1512 | h1512
                        · linarith only [h0, h1453, h1460, h1512, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1514 | h1514
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1515 | h1515
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1516 | h1516
                              · linarith only [h1453, h1460, h1510, h1516, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1518 | h1518
                                · linarith only [h1453, h1460, h1510, h1514, h1518, hlam]
                                · rcases h0bigk with h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c | h1520c
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, hlam, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, h1452, h1509, h1515, h1518, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, h1453, h1510, h1514, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, h1452, h1509, h1515, h1518, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    rcases p1520_3 (m.d 0 1) (by simp) with h1529 | h1529
                                    · linarith only [h0, h1529, hlam]
                                    · linarith only [h1453, h1529, hlam]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    rcases p1520_3 (m.d 0 1) (by simp) with h1532 | h1532
                                    · linarith only [h0, h1532, hlam]
                                    · linarith only [h1454, h1532, hlam]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1452, hlam, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1455, hlam, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, h1452, h1453, h1510, h1514, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, h1452, h1454, h1510, h1512, h1514, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1453, hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1456, hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1458, hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1460, hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1454, hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1457, hlam, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h1459, hlam, p1520_0]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [h0, h1453, h1454, h1510, h1514, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1520_1]
                                  · have p1520_0 := h1520c.1
                                    have p1520_1 := h1520c.2.1
                                    have p1520_2 := h1520c.2.2.1
                                    have p1520_3 := h1520c.2.2.2
                                    linarith only [hlam, p1520_0]
                            · linarith only [h0, h1452, h1459, h1514, h1515, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1458, h1460, h1514, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1457, h1511, hlam]
                    · linarith only [h0, h1510, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1455, h1509, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1555 | h1555
                · linarith only [h1458, h1459, h1555, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1557 | h1557
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1558 | h1558
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1559 | h1559
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1560 | h1560
                        · linarith only [h1555, h1560, hc04, hlam, hphi, u4elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1562 | h1562
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1563 | h1563
                            · linarith only [h0, h1452, h1459, h1557, h1563, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1565 | h1565
                              · linarith only [h1453, h1555, h1558, h1565, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1567 | h1567
                                · linarith only [h1452, h1459, h1555, h1557, h1562, h1567, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h1458, h1459, h1567, hc34, hlam, hphi, u4elo4]
                          · linarith only [h1458, h1459, h1562, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1452, h1457, h1559, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1558, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1455, h1557, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1574 | h1574
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1575 | h1575
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1576 | h1576
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1577 | h1577
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1578 | h1578
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1579 | h1579
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1580 | h1580
                          · linarith only [h0, h1452, h1458, h1576, h1580, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1582 | h1582
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1583 | h1583
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1584 | h1584
                                · rcases h0bigk with h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [hlam, p1585_0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h0, hlam, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h0, h1452, h1576, h1582, h1584, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h0, h1452, h1458, h1576, h1582, h1584, hc04, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1585_1, u4elo3]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [hlam, p1585_0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h0, h1452, h1576, h1582, h1584, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h0, h1452, h1458, h1576, h1582, h1584, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    rcases p1585_3 (m.d 0 1) (by simp) with h1595 | h1595
                                    · linarith only [h0, h1595, hlam]
                                    · linarith only [h1454, h1595, hlam]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1452, hlam, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1455, hlam, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [hlam, p1585_0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1458, hlam, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1454, h1458, h1578, h1582, h1584, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1585_1, u4elo3]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1453, hlam, p1585_0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1456, hlam, p1585_0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [hc03, hlam, hphi, ht34, p1585_1, u4elo0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [hlam, p1585_0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1454, h1458, h1578, h1582, h1584, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1585_1, u4elo3]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1454, hlam, p1585_0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1457, hlam, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1574, hlam, p1585_0]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [h1575, hlam, p1585_1]
                                  · have p1585_0 := h1585c.1
                                    have p1585_1 := h1585c.2.1
                                    have p1585_2 := h1585c.2.2.1
                                    have p1585_3 := h1585c.2.2.2
                                    linarith only [hlam, p1585_0]
                                · linarith only [h1452, h1458, h1576, h1582, h1584, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                              · linarith only [h1575, h1580, h1582, h1583, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                            · linarith only [h1458, h1574, h1582, hc23, hlam, hphi, ht34, u4elo3]
                        · linarith only [h1458, h1575, h1579, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h1457, h1578, hlam]
                    · linarith only [h0, h1452, h1576, h1577, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1455, h1576, hlam]
                · linarith only [h1458, h1574, h1575, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1621 | h1621
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1622 | h1622
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1623 | h1623
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1624 | h1624
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1625 | h1625
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1626 | h1626
                          · linarith only [h1452, h1458, h1622, h1626, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1628 | h1628
                            · linarith only [h1452, h1574, h1622, h1628, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1630 | h1630
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1631 | h1631
                                · rcases h0bigk with h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, h1452, h1574, h1622, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    rcases p1632_3 (m.d 0 1) (by simp) with h1640 | h1640
                                    · linarith only [h0, h1640, hlam]
                                    · linarith only [h1452, h1640, hlam]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, h1453, h1623, h1630, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    rcases p1632_3 (m.d 0 1) (by simp) with h1644 | h1644
                                    · linarith only [h0, h1644, hlam]
                                    · linarith only [h1454, h1644, hlam]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1452, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1455, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1458, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1574, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1453, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1456, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1452, h1622, hc23, hlam, hphi, ht34, p1632_1, u4elo0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1452, h1458, h1574, h1622, hc23, hlam, hphi, ht34, p1632_1, u4elo3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1454, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1457, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, h1452, h1454, h1622, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1621, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                · linarith only [h1452, h1458, h1622, h1631, hc23, hlam, hphi, ht34, u4elo4]
                              · linarith only [h1453, h1625, h1630, hc24, hlam, hphi, u4elo0]
                        · linarith only [h1458, h1621, h1625, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h1457, h1624, hlam]
                    · linarith only [h0, h1623, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1455, h1622, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1668 | h1668
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1669 | h1669
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1670 | h1670
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1671 | h1671
                        · linarith only [h1458, h1621, h1671, hc03, hlam, hphi, ht34, u4elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1673 | h1673
                          · linarith only [h1452, h1458, h1621, h1668, h1673, hc34, hlam, hphi, u4elo4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1675 | h1675
                            · linarith only [h0, h1454, h1574, h1669, h1671, h1673, h1675, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1677 | h1677
                              · linarith only [h1453, h1621, h1669, h1677, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1679 | h1679
                                · linarith only [h1621, h1679, hc04, hlam, hphi, u4elo3]
                                · linarith only [h1452, h1458, h1668, h1679, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1457, h1670, hlam]
                    · linarith only [h0, h1669, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1455, h1668, hlam]
          · linarith only [h0, h1454, h1457, hlam]
        · linarith only [h0, h1453, h1456, hc14, hlam, hphi, u4elo2]
      · linarith only [h0, h1452, h1455, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1688 | h1688
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1689 | h1689
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1690 | h1690
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1691 | h1691
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1692 | h1692
              · linarith only [h1452, h1454, h1692, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1694 | h1694
                · linarith only [h1453, h1454, h1694, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1696 | h1696
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1697 | h1697
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1698 | h1698
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1699 | h1699
                        · linarith only [h1453, h1454, h1694, h1698, h1699, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1452, h1454, h1699, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1452, h1690, h1696, h1698, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1452, h1696, h1697, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1452, h1688, h1696, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1705 | h1705
              · linarith only [h1452, h1454, h1705, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1707 | h1707
                · linarith only [h1453, h1454, h1707, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1709 | h1709
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1710 | h1710
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1711 | h1711
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1712 | h1712
                        · linarith only [h1453, h1454, h1691, h1707, h1712, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1452, h1454, h1709, h1712, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1452, h1690, h1707, h1709, h1711, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1452, h1709, h1710, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1688, h1709, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1718 | h1718
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1719 | h1719
              · linarith only [h0, h1452, h1690, h1719, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1721 | h1721
                · linarith only [h0, h1453, h1690, h1721, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1723 | h1723
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1724 | h1724
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1725 | h1725
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1726 | h1726
                        · linarith only [h0, h1453, h1690, h1721, h1725, h1726, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1452, h1690, h1723, h1725, h1726, hc23, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1729 | h1729
                        · linarith only [h1721, h1729, hc04, hlam, hphi, u4elo1]
                        · linarith only [h0, h1452, h1723, h1725, h1729, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1452, h1723, h1724, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1688, h1723, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1734 | h1734
              · linarith only [h1452, h1454, h1734, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1736 | h1736
                · linarith only [h0, h1453, h1690, h1736, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1738 | h1738
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1739 | h1739
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1740 | h1740
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1741 | h1741
                        · linarith only [h0, h1453, h1690, h1718, h1736, h1740, h1741, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1452, h1454, h1738, h1741, hc23, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1744 | h1744
                        · linarith only [h0, h1453, h1690, h1736, h1740, h1744, hc02, hc25, hlam, hphi]
                        · linarith only [h0, h1452, h1740, h1744, hc13, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1452, h1738, h1739, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1688, h1690, h1736, h1738, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
        · linarith only [h0, h1452, h1689, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h1452, h1688, hlam]
  · linarith only [h1452, h1453, hc13, hlam, hphi, ht34, u4elo1]

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1452 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1752 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1753 | h1753
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1754 | h1754
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1755 | h1755
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1756 | h1756
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1757 | h1757
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1758 | h1758
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1759 | h1759
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1760 | h1760
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1761 | h1761
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1762 | h1762
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1763 | h1763
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1764 | h1764
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1765 | h1765
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1766 | h1766
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1767 | h1767
                              · rcases h0bigk with h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h0, hlam, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1452, hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1452, h1760, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1452, h1760, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1752, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h0, h1452, h1752, h1761, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h0, h1757, h1767, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  rcases p1768_3 (m.d 0 1) (by simp) with h1778 | h1778
                                  · linarith only [h0, h1778, hlam]
                                  · linarith only [h1753, h1778, hlam]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1752, h1761, h1764, h1767, hc03, hc45, hlam, hphi, ht0b, ht5b, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1754, hlam, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h0, h1752, h1754, h1761, h1764, h1767, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  rcases p1768_3 (m.d 0 1) (by simp) with h1785 | h1785
                                  · linarith only [h1452, h1785, hlam]
                                  · linarith only [h1753, h1785, hlam]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1752, hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1755, hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1757, hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1768_1, u4elo0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1753, hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1756, hlam, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1758, hlam, p1768_0]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [h1759, hlam, p1768_1]
                                · have p1768_0 := h1768c.1
                                  have p1768_1 := h1768c.2.1
                                  have p1768_2 := h1768c.2.2.1
                                  have p1768_3 := h1768c.2.2.2
                                  linarith only [hlam, p1768_0]
                              · linarith only [h1759, h1767, hc34, hlam, hphi, u4elo0]
                            · linarith only [h1759, h1766, hc24, hlam, hphi, u4elo0]
                          · linarith only [h1758, h1759, h1764, h1765, hc34, hlam, hphi, u4elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1801 | h1801
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1802 | h1802
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1803 | h1803
                              · rcases h0bigk with h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h0, hlam, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1452, hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1452, h1757, h1760, h1764, h1801, h1803, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1452, h1760, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h0, h1452, h1752, h1757, h1764, h1801, h1803, hc12, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1804_1, u4elo0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h0, h1757, h1764, h1801, h1803, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  rcases p1804_3 (m.d 0 1) (by simp) with h1814 | h1814
                                  · linarith only [h0, h1814, hlam]
                                  · linarith only [h1753, h1814, hlam]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1752, h1757, h1764, h1801, h1803, hc03, hc45, hlam, hphi, ht0b, ht5b, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1754, hlam, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1452, h1757, h1760, h1764, h1801, h1803, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  rcases p1804_3 (m.d 0 1) (by simp) with h1821 | h1821
                                  · linarith only [h1452, h1821, hlam]
                                  · linarith only [h1753, h1821, hlam]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1752, hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1755, hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1757, hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1753, h1762, h1801, h1803, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1804_1, u4elo0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1753, hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1756, hlam, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1758, hlam, p1804_0]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [h1759, hlam, p1804_1]
                                · have p1804_0 := h1804c.1
                                  have p1804_1 := h1804c.2.1
                                  have p1804_2 := h1804c.2.2.1
                                  have p1804_3 := h1804c.2.2.2
                                  linarith only [hlam, p1804_0]
                              · linarith only [h1764, h1801, h1803, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h1759, h1764, h1801, h1802, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1836 | h1836
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1837 | h1837
                              · rcases h0bigk with h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c | h1838c
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h0, hlam, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1452, hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1452, h1760, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1452, h1760, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h0, h1452, h1753, h1758, h1801, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h0, h1755, h1836, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h0, h1758, h1801, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1753, h1758, h1801, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1754, hlam, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1452, h1755, h1760, h1836, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1452, h1758, h1760, h1801, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1752, hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1755, hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1757, hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1752, h1758, h1801, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1753, hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1756, hlam, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1758, hlam, p1838_0]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [h1759, hlam, p1838_1]
                                · have p1838_0 := h1838c.1
                                  have p1838_1 := h1838c.2.1
                                  have p1838_2 := h1838c.2.2.1
                                  have p1838_3 := h1838c.2.2.2
                                  linarith only [hlam, p1838_0]
                              · linarith only [h1761, h1836, h1837, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1759, h1836, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1759, h1763, hc14, hlam, hphi, u4elo0]
                    · linarith only [h0, h1756, h1762, hlam]
                  · linarith only [h1452, h1760, h1761, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1753, h1754, h1760, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1870 | h1870
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1871 | h1871
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1872 | h1872
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1873 | h1873
                      · linarith only [h1452, h1752, h1759, h1873, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1875 | h1875
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1876 | h1876
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1877 | h1877
                            · linarith only [h1752, h1759, h1871, h1877, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1879 | h1879
                              · linarith only [h1759, h1879, hc04, hlam, hphi, u4elo3]
                              · rcases h0bigk with h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c | h1881c
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h0, hlam, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1452, hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1452, h1752, h1870, h1871, h1875, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1452, h1752, h1759, h1870, h1871, h1875, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h0, h1452, h1753, h1871, h1873, h1875, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  rcases p1881_3 (m.d 0 1) (by simp) with h1890 | h1890
                                  · linarith only [h0, h1890, hlam]
                                  · linarith only [h1752, h1890, hlam]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  rcases p1881_3 (m.d 0 1) (by simp) with h1893 | h1893
                                  · linarith only [h0, h1893, hlam]
                                  · linarith only [h1753, h1893, hlam]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1753, h1871, h1873, h1875, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1754, hlam, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  rcases p1881_3 (m.d 0 1) (by simp) with h1899 | h1899
                                  · linarith only [h1452, h1899, hlam]
                                  · linarith only [h1752, h1899, hlam]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  rcases p1881_3 (m.d 0 1) (by simp) with h1902 | h1902
                                  · linarith only [h1452, h1902, hlam]
                                  · linarith only [h1753, h1902, hlam]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1752, hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1755, hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1757, hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1759, hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1753, hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1756, hlam, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h1758, hlam, p1881_0]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [h0, h1752, h1753, h1871, h1875, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1881_1]
                                · have p1881_0 := h1881c.1
                                  have p1881_1 := h1881c.2.1
                                  have p1881_2 := h1881c.2.2.1
                                  have p1881_3 := h1881c.2.2.2
                                  linarith only [hlam, p1881_0]
                          · linarith only [h1758, h1759, h1875, h1876, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1757, h1759, h1875, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1756, h1872, hlam]
                  · linarith only [h1452, h1870, h1871, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1754, h1870, hlam]
            · linarith only [h1452, h1753, h1758, hlam]
          · linarith only [h1452, h1752, h1757, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h1753, h1756, hlam]
      · linarith only [h1452, h1752, h1754, h1755, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1924 | h1924
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1925 | h1925
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1926 | h1926
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1927 | h1927
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1928 | h1928
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1929 | h1929
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1930 | h1930
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1931 | h1931
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1932 | h1932
                      · linarith only [h0, h1752, h1754, h1929, h1932, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1928, h1930, h1932, hc24, hlam, hphi, u4elo0]
                    · linarith only [h0, h1754, h1929, h1931, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h1754, h1929, h1930, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1937 | h1937
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1938 | h1938
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1939 | h1939
                      · linarith only [h0, h1752, h1929, h1939, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1752, h1928, h1929, h1939, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1752, h1754, h1925, h1928, h1938, hc03, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1752, h1937, hc14, hlam, hphi, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1944 | h1944
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1945 | h1945
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1946 | h1946
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1947 | h1947
                      · linarith only [h1752, h1928, h1947, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1949 | h1949
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1950 | h1950
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1951 | h1951
                            · linarith only [h1752, h1928, h1945, h1951, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1953 | h1953
                              · linarith only [h1752, h1928, h1945, h1949, h1953, hlam]
                              · rcases h0bigk with h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h0, hlam, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1452, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h0, h1752, h1754, h1945, h1949, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h0, h1754, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1754, hc01, hc23, hlam, hphi, ht12, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1754, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1752, h1754, h1945, h1949, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1753, h1754, h1945, h1947, h1949, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1753, h1945, h1947, h1949, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h0, h1452, h1753, h1944, h1945, h1947, h1949, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1752, h1754, h1944, h1945, h1949, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1753, h1754, h1944, h1945, h1947, h1949, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1752, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1924, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1926, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1928, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1753, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1925, hlam, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1927, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h0, h1752, h1753, h1945, h1949, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                          · linarith only [h1754, h1927, h1950, hlam]
                        · linarith only [h0, h1754, h1949, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h1754, h1925, h1946, hc12, hc23, hlam, hphi]
                  · linarith only [h1754, h1944, h1945, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1985 | h1985
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1986 | h1986
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1987 | h1987
                      · linarith only [h0, h1752, h1944, h1987, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1989 | h1989
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1990 | h1990
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1991 | h1991
                            · linarith only [h1752, h1928, h1985, h1991, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1993 | h1993
                              · linarith only [h1928, h1993, hc04, hlam, hphi, u4elo3]
                              · rcases h0bigk with h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h0, hlam, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1452, hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h0, h1752, h1985, h1989, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h0, h1752, h1928, h1944, h1985, h1989, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1753, h1754, hc03, hc15, hlam, hphi, ht0b, ht5b, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1754, hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h0, h1752, h1944, h1985, h1989, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h0, h1752, h1928, h1944, h1985, h1989, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1752, h1754, h1985, h1989, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1754, hc02, hc23, hlam, hphi, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  rcases p1995_3 (m.d 0 1) (by simp) with h2009 | h2009
                                  · linarith only [h1452, h2009, hlam]
                                  · linarith only [h1752, h2009, hlam]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  rcases p1995_3 (m.d 0 1) (by simp) with h2012 | h2012
                                  · linarith only [h1452, h2012, hlam]
                                  · linarith only [h1753, h2012, hlam]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1752, hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1924, hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1926, hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1928, hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1753, hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1925, hlam, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h1927, hlam, p1995_0]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [h0, h1752, h1753, h1944, h1985, h1989, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1995_1]
                                · have p1995_0 := h1995c.1
                                  have p1995_1 := h1995c.2.1
                                  have p1995_2 := h1995c.2.2.1
                                  have p1995_3 := h1995c.2.2.2
                                  linarith only [hlam, p1995_0]
                          · linarith only [h0, h1944, h1990, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h1753, h1944, h1985, h1987, h1989, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1752, h1925, h1985, h1986, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1985, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h1452, h1753, h1927, hlam]
          · linarith only [h0, h1752, h1754, h1926, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h1753, h1925, hlam]
      · linarith only [h0, h1752, h1924, hc14, hlam, hphi, u4elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2033 | h2033
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2034 | h2034
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2035 | h2035
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2036 | h2036
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2037 | h2037
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2038 | h2038
              · linarith only [h1752, h1753, h2038, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2040 | h2040
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2041 | h2041
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2042 | h2042
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2043 | h2043
                      · linarith only [h1752, h1753, h2038, h2043, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1752, h1753, h2041, h2043, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h2033, h2035, h2038, h2042, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h1452, h2040, h2041, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1752, h2033, h2040, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2049 | h2049
              · linarith only [h1452, h1752, h2037, h2049, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2051 | h2051
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2052 | h2052
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2053 | h2053
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2054 | h2054
                      · linarith only [h1452, h1752, h2049, h2054, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1752, h1753, h2052, h2054, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1752, h2035, h2049, h2052, h2053, hc24, hlam, hphi, u4elo4]
                  · linarith only [h1452, h2051, h2052, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1752, h2033, h2051, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h1452, h1752, h2036, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2061 | h2061
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2062 | h2062
            · linarith only [h2033, h2035, h2062, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2064 | h2064
              · linarith only [h0, h1752, h2035, h2064, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2066 | h2066
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2067 | h2067
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2068 | h2068
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2069 | h2069
                      · linarith only [h2064, h2069, hc04, hlam, hphi, u4elo1]
                      · linarith only [h2033, h2035, h2068, h2069, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2072 | h2072
                      · linarith only [h0, h1752, h2068, h2072, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h1752, h1753, h2072, hc14, hlam, hphi, u4elo4]
                  · linarith only [h1452, h1752, h2066, h2067, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h1752, h2033, h2066, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h1452, h1752, h2061, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h1752, h2034, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2079 | h2079
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2080 | h2080
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2081 | h2081
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2082 | h2082
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2083 | h2083
              · linarith only [h1752, h1753, h2083, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2085 | h2085
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2086 | h2086
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2087 | h2087
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2088 | h2088
                      · linarith only [h1752, h1753, h2033, h2080, h2083, h2085, h2088, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1752, h1753, h2086, h2088, hc24, hlam, hphi, u4elo4]
                    · linarith only [h2033, h2080, h2087, hc12, hc23, hlam, hphi]
                  · linarith only [h2033, h2085, h2086, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2093 | h2093
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2094 | h2094
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2095 | h2095
                      · linarith only [h1752, h1753, h2083, h2094, h2095, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1752, h1753, h2093, h2095, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h2080, h2094, hlam]
                  · linarith only [h0, h2093, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h2033, h2080, h2082, hlam]
          · linarith only [h1752, h1753, h2033, h2080, h2081, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2102 | h2102
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2103 | h2103
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2104 | h2104
              · linarith only [h0, h1752, h2080, h2104, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2106 | h2106
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2107 | h2107
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2108 | h2108
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2109 | h2109
                      · linarith only [h0, h1752, h2033, h2104, h2106, h2109, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1752, h2080, h2107, h2108, h2109, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1752, h2033, h2106, h2107, h2108, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1752, h2033, h2106, h2107, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2114 | h2114
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2115 | h2115
                    · linarith only [h0, h1752, h2080, h2106, h2114, h2115, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2117 | h2117
                      · linarith only [h0, h1752, h2106, h2117, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1752, h2115, h2117, hc14, hlam, hphi, u4elo4]
                  · linarith only [h0, h1752, h2114, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2121 | h2121
              · linarith only [h1452, h1752, h2103, h2121, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2123 | h2123
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2124 | h2124
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2125 | h2125
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2126 | h2126
                      · linarith only [h0, h1752, h2033, h2121, h2123, h2126, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1752, h2080, h2124, h2125, h2126, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1752, h2033, h2123, h2124, h2125, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1752, h2033, h2123, h2124, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2131 | h2131
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2132 | h2132
                    · linarith only [h0, h1752, h2080, h2123, h2131, h2132, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2134 | h2134
                      · linarith only [h0, h1752, h2103, h2121, h2123, h2134, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h1752, h2132, h2134, hc14, hlam, hphi, u4elo4]
                  · linarith only [h0, h1752, h2131, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h1752, h2033, h2102, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h1752, h2079, hc14, hlam, hphi, u4elo2]

end R2N4
