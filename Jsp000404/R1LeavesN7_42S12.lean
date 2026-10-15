import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_42S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1455 | h1455
  · linarith only [h0, h1, h1455, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1457 | h1457
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1458 | h1458
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1459 | h1459
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1460 | h1460
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1461 | h1461
            · linarith only [h0, h1, h1455, h1461, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1463 | h1463
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1464 | h1464
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1465 | h1465
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1466 | h1466
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1467 | h1467
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1468 | h1468
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1469 | h1469
                          · linarith only [h0, h1, h1461, h1463, h1469, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1471 | h1471
                            · linarith only [h0, h1, h1461, h1463, h1465, h1469, h1471, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases h2bigk with h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h0, h1, h1461, hc12, hc23, hlam, hphi, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1455, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h0, h1, h1461, h1467, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h0, h1, h1461, h1468, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h0, hlam, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1461, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h0, h1, h1461, h1467, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h0, h1, h1461, h1468, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                rcases p1473_3 (m.d 0 2) (by simp) with h1487 | h1487
                                · linarith only [h1455, h1487, hlam]
                                · linarith only [h1457, h1487, hlam]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                rcases p1473_3 (m.d 0 2) (by simp) with h1490 | h1490
                                · linarith only [h1455, h1490, hlam]
                                · linarith only [h1458, h1490, hlam]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1457, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1463, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1467, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1469, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1458, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1464, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h1468, hlam, p1473_0]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [h0, h1464, h1467, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1473_1]
                              · have p1473_0 := h1473c.1
                                have p1473_1 := h1473c.2.1
                                have p1473_2 := h1473c.2.2.1
                                have p1473_3 := h1473c.2.2.2
                                linarith only [hlam, p1473_0]
                        · linarith only [h0, h1, h1461, h1468, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h1461, h1463, h1467, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h1463, h1466, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h1463, h1465, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1463, h1464, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h1, h1457, h1461, h1463, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h1457, h1460, hc24, hlam, hphi, ht45, u5elo3]
        · linarith only [h0, h1, h1457, h1459, hlam]
      · linarith only [h1457, h1458, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1512 | h1512
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1513 | h1513
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1514 | h1514
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1515 | h1515
            · linarith only [h0, h1455, h1512, h1515, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1517 | h1517
              · linarith only [h0, h1, h1457, h1517, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1519 | h1519
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1520 | h1520
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1521 | h1521
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1522 | h1522
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1523 | h1523
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1524 | h1524
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1525 | h1525
                            · rcases h2bigk with h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1519, h1523, h1525, hc02, hc45, hlam, hphi, ht0b, ht5b, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1455, hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1457, hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h0, h1, h1523, h1525, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h0, hlam, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1515, hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1517, hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h0, h1, h1515, h1523, h1525, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h0, h1457, h1519, h1523, h1525, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                rcases p1526_3 (m.d 0 2) (by simp) with h1541 | h1541
                                · linarith only [h1455, h1541, hlam]
                                · linarith only [h1512, h1541, hlam]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h0, h1519, h1523, h1525, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1519, h1523, h1525, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1522, hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                rcases p1526_3 (m.d 0 2) (by simp) with h1548 | h1548
                                · linarith only [h1457, h1548, hlam]
                                · linarith only [h1512, h1548, hlam]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1512, hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1519, hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1523, hlam, p1526_0]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [h1524, hlam, p1526_1]
                              · have p1526_0 := h1526c.1
                                have p1526_1 := h1526c.2.1
                                have p1526_2 := h1526c.2.2.1
                                have p1526_3 := h1526c.2.2.2
                                linarith only [hlam, p1526_0]
                            · linarith only [h0, h1, h1515, h1519, h1524, h1525, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1457, h1524, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1, h1515, h1519, h1523, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h1515, h1519, h1522, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h1, h1519, h1521, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h1, h1513, h1520, hlam]
                · linarith only [h1457, h1512, h1519, hc12, hc24, hlam, hphi]
          · linarith only [h0, h1, h1512, h1514, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1564 | h1564
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1565 | h1565
            · linarith only [h0, h1455, h1512, h1565, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1567 | h1567
              · linarith only [h0, h1457, h1567, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1569 | h1569
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1570 | h1570
                  · linarith only [h0, h1, h1513, h1565, h1570, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1569, h1570, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h1455, h1512, h1569, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h1512, h1564, hc25, hlam, hphi, u5elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1575 | h1575
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1576 | h1576
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1577 | h1577
            · linarith only [h0, h1, h1455, h1577, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1579 | h1579
              · linarith only [h0, h1457, h1579, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1581 | h1581
                · linarith only [h0, h1512, h1581, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1583 | h1583
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1584 | h1584
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1585 | h1585
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1586 | h1586
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1587 | h1587
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1588 | h1588
                            · rcases h2bigk with h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1512, hc12, hlam, hphi, ht23, ht34, ht45, p1589_1, u5elo2]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1455, hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1457, hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1512, hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h0, hlam, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1577, hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1579, hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1581, hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h0, h1457, hc12, hc23, hlam, hphi, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h0, h1512, hc12, hc23, hlam, hphi, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h0, hc12, hc24, hlam, hphi, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hc12, hc24, hlam, hphi, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1585, hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h0, h1512, h1585, hc12, hc23, hlam, hphi, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h0, hc12, hc25, hlam, hphi, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1589_1, u5elo2]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1586, hlam, p1589_0]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [h1587, hlam, p1589_1]
                              · have p1589_0 := h1589c.1
                                have p1589_1 := h1589c.2.1
                                have p1589_2 := h1589c.2.2.1
                                have p1589_3 := h1589c.2.2.2
                                linarith only [hlam, p1589_0]
                            · rcases h2bigk with h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c | h1615c
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h0, h1, h1577, hc12, hc23, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1455, hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1457, hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1512, hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h0, hlam, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1577, hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1579, hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1581, hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hc02, hc23, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hc12, hc23, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h0, h1457, hc12, hc23, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h0, h1512, hc12, hc23, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h0, hc12, hc24, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hc12, hc24, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1585, hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h0, h1512, h1585, hc12, hc23, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h0, hc12, hc25, hlam, hphi, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1615_1, u5elo2]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1586, hlam, p1615_0]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [h1587, hlam, p1615_1]
                              · have p1615_0 := h1615c.1
                                have p1615_1 := h1615c.2.1
                                have p1615_2 := h1615c.2.2.1
                                have p1615_3 := h1615c.2.2.2
                                linarith only [hlam, p1615_0]
                          · linarith only [h0, h1457, h1587, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h1, h1577, h1586, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h1, h1577, h1585, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1576, h1584, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1457, h1575, h1583, hc12, hc24, hlam, hphi]
          · linarith only [h0, h1, h1576, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1647 | h1647
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1648 | h1648
            · linarith only [h0, h1, h1575, h1648, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1650 | h1650
              · linarith only [h0, h1512, h1650, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1652 | h1652
                · linarith only [h0, h1512, h1652, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1654 | h1654
                  · linarith only [h0, h1, h1575, h1648, h1654, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1654, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h0, h1, h1647, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0 m hb2 hb3 hb5 h0 h1
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x1 m hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1658 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1659 | h1659
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1660 | h1660
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1661 | h1661
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1662 | h1662
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1663 | h1663
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1664 | h1664
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1665 | h1665
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1666 | h1666
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1667 | h1667
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1668 | h1668
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1669 | h1669
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1670 | h1670
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1671 | h1671
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1672 | h1672
                            · linarith only [h0, h1658, h1664, h1669, h1672, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h1658, h1665, h1667, h1671, h1672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1675 | h1675
                            · linarith only [h0, h1658, h1662, h1671, h1675, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h2bigk with h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h0, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h0, h1670, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1677_1]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                rcases p1677_3 (m.d 0 2) (by simp) with h1681 | h1681
                                · rcases p1677_3 (m.d 1 2) (by simp) with h1682 | h1682
                                  · rcases p1677_3 (m.d 2 3) (by simp) with h1683 | h1683
                                    · linarith only [h1659, h1683, hlam]
                                    · linarith only [h1669, h1683, hlam]
                                  · linarith only [h1665, h1682, hlam]
                                · linarith only [h1681, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                rcases p1677_3 (m.d 0 2) (by simp) with h1688 | h1688
                                · rcases p1677_3 (m.d 1 2) (by simp) with h1689 | h1689
                                  · rcases p1677_3 (m.d 2 3) (by simp) with h1690 | h1690
                                    · linarith only [h1659, h1690, hlam]
                                    · linarith only [h1670, h1690, hlam]
                                  · linarith only [h1666, h1689, hlam]
                                · linarith only [h1688, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1677_1]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1670, h1675, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1677_1]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                rcases p1677_3 (m.d 0 2) (by simp) with h1698 | h1698
                                · linarith only [h0, h1698, hlam]
                                · linarith only [h1660, h1698, hlam]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                rcases p1677_3 (m.d 0 2) (by simp) with h1701 | h1701
                                · linarith only [h0, h1701, hlam]
                                · linarith only [h1661, h1701, hlam]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1659, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1664, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1658, h1664, h1669, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1677_1]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h0, h1658, h1664, h1670, h1675, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1677_1]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1660, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1665, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1669, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1671, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1661, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1666, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1670, hlam, p1677_0]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [h1669, hc34, hlam, hphi, ht45, p1677_1, u5elo2]
                              · have p1677_0 := h1677c.1
                                have p1677_1 := h1677c.2.1
                                have p1677_2 := h1677c.2.2.1
                                have p1677_3 := h1677c.2.2.2
                                linarith only [hlam, p1677_0]
                        · linarith only [h0, h1658, h1668, h1670, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1658, h1667, h1669, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1667, h1668, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1722 | h1722
                    · linarith only [h0, h1658, h1662, h1667, h1722, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1724 | h1724
                      · linarith only [h1664, h1667, h1724, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1726 | h1726
                        · linarith only [h1664, h1722, h1726, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1728 | h1728
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1729 | h1729
                            · rcases h2bigk with h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h0, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                rcases p1730_3 (m.d 0 2) (by simp) with h1733 | h1733
                                · rcases p1730_3 (m.d 1 2) (by simp) with h1734 | h1734
                                  · rcases p1730_3 (m.d 2 3) (by simp) with h1735 | h1735
                                    · linarith only [h1735, hlam, p1730_0]
                                    · rcases p1730_3 (m.d 2 4) (by simp) with h1737 | h1737
                                      · linarith only [h1660, h1737, hlam]
                                      · linarith only [h1724, h1737, hlam]
                                  · linarith only [h1664, h1734, hlam]
                                · linarith only [h1733, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h0, h1728, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1730_1]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                rcases p1730_3 (m.d 0 2) (by simp) with h1743 | h1743
                                · rcases p1730_3 (m.d 1 2) (by simp) with h1744 | h1744
                                  · rcases p1730_3 (m.d 2 3) (by simp) with h1745 | h1745
                                    · linarith only [h1659, h1745, hlam]
                                    · rcases p1730_3 (m.d 2 4) (by simp) with h1747 | h1747
                                      · linarith only [h1660, h1747, hlam]
                                      · linarith only [h1728, h1747, hlam]
                                  · linarith only [h1666, h1744, hlam]
                                · linarith only [h1743, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h0, h1658, h1662, h1664, h1722, h1729, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1730_1]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                rcases p1730_3 (m.d 0 2) (by simp) with h1754 | h1754
                                · linarith only [h0, h1754, hlam]
                                · linarith only [h1659, h1754, hlam]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1728, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1730_1]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                rcases p1730_3 (m.d 0 2) (by simp) with h1758 | h1758
                                · linarith only [h0, h1758, hlam]
                                · linarith only [h1661, h1758, hlam]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1659, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1664, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1724, hlam, p1730_1]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1726, hlam, p1730_1]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1660, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1665, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1660, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1730_1]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1658, h1662, h1665, h1667, h1726, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1730_1]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1661, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1666, hlam, p1730_0]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, ht45, p1730_1, u5elo2]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [h1728, hlam, p1730_1]
                              · have p1730_0 := h1730c.1
                                have p1730_1 := h1730c.2.1
                                have p1730_2 := h1730c.2.2.1
                                have p1730_3 := h1730c.2.2.2
                                linarith only [hlam, p1730_0]
                            · linarith only [h1664, h1667, h1729, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1777 | h1777
                            · linarith only [h0, h1658, h1662, h1728, h1777, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1664, h1667, h1777, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h1666, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h1658, h1660, h1662, h1665, hlam]
            · linarith only [h0, h1659, h1664, hlam]
          · linarith only [h1662, h1663, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1784 | h1784
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1785 | h1785
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1786 | h1786
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1787 | h1787
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1788 | h1788
                  · linarith only [h1658, h1662, h1784, h1788, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1790 | h1790
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1791 | h1791
                      · linarith only [h1658, h1662, h1785, h1791, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1793 | h1793
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1794 | h1794
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1795 | h1795
                            · rcases h2bigk with h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h0, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h0, h1793, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h0, h1791, h1793, h1795, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                rcases p1796_3 (m.d 0 2) (by simp) with h1801 | h1801
                                · rcases p1796_3 (m.d 1 2) (by simp) with h1802 | h1802
                                  · rcases p1796_3 (m.d 2 3) (by simp) with h1803 | h1803
                                    · linarith only [h1659, h1803, hlam]
                                    · linarith only [h1793, h1803, hlam]
                                  · linarith only [h1787, h1802, hlam]
                                · linarith only [h1801, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1793, h1795, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1791, h1793, h1795, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                rcases p1796_3 (m.d 0 2) (by simp) with h1812 | h1812
                                · linarith only [h0, h1812, hlam]
                                · linarith only [h1661, h1812, hlam]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1659, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1785, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1791, hlam, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1658, h1785, h1793, h1795, hc01, hc45, hlam, hphi, ht0b, ht5b, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1660, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1786, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h0, h1660, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h0, h1660, h1793, h1795, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1661, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1787, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1793, hlam, p1796_0]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [h1794, hlam, p1796_1]
                              · have p1796_0 := h1796c.1
                                have p1796_1 := h1796c.2.1
                                have p1796_2 := h1796c.2.2.1
                                have p1796_3 := h1796c.2.2.2
                                linarith only [hlam, p1796_0]
                            · linarith only [h1662, h1795, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h1791, h1793, h1794, hc35, hlam, hphi, u5elo4]
                        · linarith only [h0, h1658, h1790, h1793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1662, h1784, h1790, hc13, hc34, hlam, hphi]
                · linarith only [h0, h1787, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h1658, h1660, h1785, h1786, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h1659, h1785, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1837 | h1837
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1838 | h1838
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1839 | h1839
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1840 | h1840
                  · linarith only [h1658, h1784, h1840, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1842 | h1842
                    · linarith only [h1658, h1784, h1842, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1844 | h1844
                      · linarith only [h1659, h1662, h1844, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1846 | h1846
                        · linarith only [h1658, h1784, h1837, h1846, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1848 | h1848
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1849 | h1849
                            · rcases h2bigk with h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h0, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                rcases p1850_3 (m.d 0 2) (by simp) with h1853 | h1853
                                · rcases p1850_3 (m.d 1 2) (by simp) with h1854 | h1854
                                  · rcases p1850_3 (m.d 2 3) (by simp) with h1855 | h1855
                                    · linarith only [h1855, hlam, p1850_0]
                                    · rcases p1850_3 (m.d 2 4) (by simp) with h1857 | h1857
                                      · linarith only [h1660, h1857, hlam]
                                      · linarith only [h1844, h1857, hlam]
                                  · linarith only [h1837, h1854, hlam]
                                · linarith only [h1853, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h0, h1848, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1850_1]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                rcases p1850_3 (m.d 0 2) (by simp) with h1863 | h1863
                                · rcases p1850_3 (m.d 1 2) (by simp) with h1864 | h1864
                                  · rcases p1850_3 (m.d 2 3) (by simp) with h1865 | h1865
                                    · linarith only [h1659, h1865, hlam]
                                    · rcases p1850_3 (m.d 2 4) (by simp) with h1867 | h1867
                                      · linarith only [h1660, h1867, hlam]
                                      · linarith only [h1848, h1867, hlam]
                                  · linarith only [h1839, h1864, hlam]
                                · linarith only [h1863, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1850_1]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                rcases p1850_3 (m.d 0 2) (by simp) with h1874 | h1874
                                · linarith only [h0, h1874, hlam]
                                · linarith only [h1659, h1874, hlam]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1848, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1850_1]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                rcases p1850_3 (m.d 0 2) (by simp) with h1878 | h1878
                                · linarith only [h0, h1878, hlam]
                                · linarith only [h1661, h1878, hlam]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1659, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1837, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1844, hlam, p1850_1]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1846, hlam, p1850_1]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1660, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1838, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1660, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1850_1]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h0, h1660, h1846, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1850_1]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1661, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1839, hlam, p1850_0]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, ht45, p1850_1, u5elo2]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [h1848, hlam, p1850_1]
                              · have p1850_0 := h1850c.1
                                have p1850_1 := h1850c.2.1
                                have p1850_2 := h1850c.2.2.1
                                have p1850_3 := h1850c.2.2.2
                                linarith only [hlam, p1850_0]
                            · linarith only [h1662, h1849, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1897 | h1897
                            · rcases h2bigk with h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h0, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                rcases p1898_3 (m.d 0 2) (by simp) with h1901 | h1901
                                · rcases p1898_3 (m.d 1 2) (by simp) with h1902 | h1902
                                  · rcases p1898_3 (m.d 2 3) (by simp) with h1903 | h1903
                                    · linarith only [h1903, hlam, p1898_0]
                                    · rcases p1898_3 (m.d 2 4) (by simp) with h1905 | h1905
                                      · linarith only [h1660, h1905, hlam]
                                      · linarith only [h1844, h1905, hlam]
                                  · linarith only [h1837, h1902, hlam]
                                · linarith only [h1901, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                rcases p1898_3 (m.d 0 2) (by simp) with h1910 | h1910
                                · rcases p1898_3 (m.d 1 2) (by simp) with h1911 | h1911
                                  · rcases p1898_3 (m.d 2 3) (by simp) with h1912 | h1912
                                    · linarith only [h1659, h1912, hlam]
                                    · rcases p1898_3 (m.d 2 4) (by simp) with h1914 | h1914
                                      · linarith only [h1914, hlam, p1898_0]
                                      · rcases p1898_3 (m.d 2 5) (by simp) with h1916 | h1916
                                        · linarith only [h1661, h1916, hlam]
                                        · linarith only [h1848, h1916, hlam]
                                  · linarith only [h1838, h1911, hlam]
                                · linarith only [h1910, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                rcases p1898_3 (m.d 0 2) (by simp) with h1921 | h1921
                                · rcases p1898_3 (m.d 1 2) (by simp) with h1922 | h1922
                                  · rcases p1898_3 (m.d 2 3) (by simp) with h1923 | h1923
                                    · linarith only [h1659, h1923, hlam]
                                    · rcases p1898_3 (m.d 2 4) (by simp) with h1925 | h1925
                                      · linarith only [h1660, h1925, hlam]
                                      · rcases p1898_3 (m.d 2 5) (by simp) with h1927 | h1927
                                        · linarith only [h1927, hlam, p1898_0]
                                        · rcases h3bigk with h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1662, h1837, hc23, hc34, hlam, hphi, p1929_1]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1662, hc23, hc34, hlam, hphi, p1929_1]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1662, hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1784, hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1658, hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h0, h1658, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1929_1]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1840, hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1842, hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1659, hlam, p1929_1]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1837, hlam, p1929_1]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1844, hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1846, hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            rcases p1929_3 (m.d 0 3) (by simp) with h1945 | h1945
                                            · linarith only [h1945, hlam, p1929_0]
                                            · rcases p1929_3 (m.d 1 3) (by simp) with h1947 | h1947
                                              · linarith only [h1840, h1947, hlam]
                                              · rcases p1929_3 (m.d 2 3) (by simp) with h1949 | h1949
                                                · linarith only [h1844, h1949, hlam]
                                                · rcases p1929_3 (m.d 3 4) (by simp) with h1951 | h1951
                                                  · rcases p1929_3 (m.d 3 5) (by simp) with h1952 | h1952
                                                    · linarith only [h1897, h1952, hlam]
                                                    · linarith only [h1784, h1952, hlam]
                                                  · linarith only [h1951, hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            rcases p1929_3 (m.d 0 3) (by simp) with h1956 | h1956
                                            · linarith only [h1662, h1956, hlam]
                                            · linarith only [h1658, h1956, hlam]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            rcases p1929_3 (m.d 0 3) (by simp) with h1959 | h1959
                                            · linarith only [h1662, h1959, hlam]
                                            · linarith only [h1659, h1959, hlam]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [hlam, p1929_0]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1784, hc03, hc34, hlam, hphi, p1929_1]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1658, hc13, hlam, hphi, ht34, ht45, p1929_1, u5elo3]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1837, hc23, hlam, hphi, ht34, ht45, p1929_1, u5elo3]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [hc23, hlam, hphi, ht34, ht45, p1929_1, u5elo3]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [h1897, hlam, p1929_1]
                                          · have p1929_0 := h1929c.1
                                            have p1929_1 := h1929c.2.1
                                            have p1929_2 := h1929c.2.2.1
                                            have p1929_3 := h1929c.2.2.2
                                            linarith only [hlam, p1929_0]
                                  · linarith only [h1839, h1922, hlam]
                                · linarith only [h1921, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1898_1]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                rcases p1898_3 (m.d 0 2) (by simp) with h1973 | h1973
                                · linarith only [h0, h1973, hlam]
                                · linarith only [h1659, h1973, hlam]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                rcases p1898_3 (m.d 0 2) (by simp) with h1976 | h1976
                                · linarith only [h0, h1976, hlam]
                                · linarith only [h1660, h1976, hlam]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                rcases p1898_3 (m.d 0 2) (by simp) with h1979 | h1979
                                · linarith only [h0, h1979, hlam]
                                · linarith only [h1661, h1979, hlam]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1659, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1837, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1844, hlam, p1898_1]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1846, hlam, p1898_1]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1660, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1838, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1848, hc23, hlam, hphi, ht34, ht45, p1898_1, u5elo2]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1848, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1661, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1839, hlam, p1898_0]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1661, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1898_1]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [h1661, h1784, hc24, hlam, hphi, ht45, p1898_1, u5elo3]
                              · have p1898_0 := h1898c.1
                                have p1898_1 := h1898c.2.1
                                have p1898_2 := h1898c.2.2.1
                                have p1898_3 := h1898c.2.2.2
                                linarith only [hlam, p1898_0]
                            · linarith only [h1658, h1662, h1837, h1897, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h1658, h1661, h1784, h1837, h1839, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h1660, h1838, hlam]
            · linarith only [h0, h1659, h1837, hlam]
      · linarith only [h1660, h1661, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2002 | h2002
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2003 | h2003
        · linarith only [h0, h1658, h1660, h2003, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2005 | h2005
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2006 | h2006
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2007 | h2007
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2008 | h2008
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2009 | h2009
                  · linarith only [h0, h1658, h1660, h2003, h2007, h2009, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2011 | h2011
                    · linarith only [h0, h1658, h1660, h2007, h2011, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h1658, h1660, h2005, h2006, h2007, h2011, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h1660, h2002, h2007, h2008, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2015 | h2015
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2016 | h2016
                  · linarith only [h1658, h2003, h2005, h2016, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2018 | h2018
                    · linarith only [h0, h1658, h2007, h2018, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1658, h2005, h2007, h2018, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h2015, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1659, h2006, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2023 | h2023
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2024 | h2024
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2025 | h2025
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2026 | h2026
                  · linarith only [h0, h1658, h1660, h2024, h2026, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2028 | h2028
                    · linarith only [h0, h1658, h1660, h2005, h2024, h2028, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2030 | h2030
                      · linarith only [h0, h1658, h1660, h2005, h2023, h2024, h2026, h2030, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2032 | h2032
                        · linarith only [h0, h1658, h1660, h2005, h2023, h2024, h2032, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2034 | h2034
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2035 | h2035
                            · rcases h2bigk with h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h0, hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h1660, h2024, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2036_1]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h1660, hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h1660, h2024, h2032, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2036_1]
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
                                rcases p2036_3 (m.d 0 2) (by simp) with h2044 | h2044
                                · linarith only [h0, h2044, hlam]
                                · linarith only [h1659, h2044, hlam]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h0, h1658, h1660, h2023, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2036_1]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                rcases p2036_3 (m.d 0 2) (by simp) with h2048 | h2048
                                · linarith only [h0, h2048, hlam]
                                · linarith only [h2002, h2048, hlam]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h1659, hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2023, hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2030, hlam, p2036_1]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2032, hlam, p2036_1]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h0, h1658, h2023, h2024, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2036_1]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2024, hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2024, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2036_1]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2024, h2032, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2036_1]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2002, hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2025, hlam, p2036_0]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, ht45, p2036_1, u5elo2]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [h2034, hlam, p2036_1]
                              · have p2036_0 := h2036c.1
                                have p2036_1 := h2036c.2.1
                                have p2036_2 := h2036c.2.2.1
                                have p2036_3 := h2036c.2.2.2
                                linarith only [hlam, p2036_0]
                            · linarith only [h1660, h2002, h2024, h2026, h2034, h2035, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1660, h2034, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h1658, h2023, h2025, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2069 | h2069
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2070 | h2070
                  · linarith only [h0, h1658, h1660, h2003, h2070, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2072 | h2072
                    · linarith only [h1658, h2005, h2072, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2074 | h2074
                      · linarith only [h0, h1658, h2023, h2024, h2070, h2074, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1658, h2024, h2074, hc13, hc34, hlam, hphi]
                · linarith only [h0, h1658, h2002, h2023, h2069, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h1659, h2023, hlam]
      · linarith only [h0, h1658, h2002, hc13, hlam, hphi, ht34, ht45, u5elo2]
  · linarith only [h0, h1658, h1659, hlam]

end R2N4
